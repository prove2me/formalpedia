-- Prove2me | solution 1 for tverberg_partition_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:30:19.629887+00:00
-- url     : https://prove2.me/submissions/55e4f12d-d77c-427a-8c78-d4a5a67eb33c

import Mathlib

open scoped BigOperators InnerProductSpace
open Set

namespace TverbergProof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inner_self_le_inner_of_min_norm {K : Set E} (hK : Convex ℝ K)
    {x : E} (hx : x ∈ K) (hmin : ∀ y ∈ K, ‖x‖ ≤ ‖y‖) :
    ∀ y ∈ K, ⟪x, x⟫_ℝ ≤ ⟪x, y⟫_ℝ := by
  letI : Nonempty K := ⟨⟨x, hx⟩⟩
  have hinf : ‖(0 : E) - x‖ = ⨅ y : K, ‖(0 : E) - y‖ := by
    simp only [zero_sub, norm_neg]
    apply le_antisymm
    · exact le_ciInf (fun y => hmin y y.property)
    · apply ciInf_le (show BddBelow (Set.range (fun y : K => ‖(y : E)‖)) from ?_) ⟨x, hx⟩
      exact ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg (y : E)⟩
  have h := (norm_eq_iInf_iff_real_inner_le_zero hK hx).mp hinf
  intro y hy
  have := h y hy
  simpa only [zero_sub, inner_neg_left, inner_sub_right, neg_sub, sub_nonpos,
    neg_le_neg_iff] using this

theorem linearIndependent_of_affineIndependent_inner_const {ι : Type*}
    {p : ι → E} (hp : AffineIndependent ℝ p) {x : E} {c : ℝ}
    (hc : c ≠ 0) (hinner : ∀ i, ⟪x, p i⟫_ℝ = c) : LinearIndependent ℝ p := by
  rw [linearIndependent_iff']
  intro s w hw i hi
  have hsum : ∑ j ∈ s, w j = 0 := by
    have h := congrArg (fun y => ⟪x, y⟫_ℝ) hw
    simp only [inner_sum, inner_smul_right, hinner, inner_zero_right,
      ← Finset.sum_mul] at h
    exact (mul_eq_zero.mp h).resolve_right hc
  exact hp.eq_zero_of_sum_eq_zero hsum hw i hi

theorem exists_small_support_of_min_norm [FiniteDimensional ℝ E]
    {K : Set E} {x : E} (hx : x ∈ convexHull ℝ K) (hne : x ≠ 0)
    (hmin : ∀ y ∈ convexHull ℝ K, ‖x‖ ≤ ‖y‖) :
    ∃ t : Finset E, (↑t : Set E) ⊆ K ∧ t.card ≤ Module.finrank ℝ E ∧
      x ∈ convexHull ℝ (↑t : Set E) := by
  classical
  obtain ⟨ι, inst, p, w, hpK, hp, hw, hsum, heq⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  letI := inst
  have hle : ∀ i, ⟪x, x⟫_ℝ ≤ ⟪x, p i⟫_ℝ := fun i =>
    inner_self_le_inner_of_min_norm (convex_convexHull ℝ K) hx hmin
      (p i) (subset_convexHull ℝ K (hpK ⟨i, rfl⟩))
  have hzero : ∑ i, w i * (⟪x, p i⟫_ℝ - ⟪x, x⟫_ℝ) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
    have h := congrArg (fun y => ⟪x, y⟫_ℝ) heq
    simp only [inner_sum, inner_smul_right] at h
    exact sub_eq_zero.mpr h
  have hinner : ∀ i, ⟪x, p i⟫_ℝ = ⟪x, x⟫_ℝ := by
    intro i
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hw j).le (sub_nonneg.mpr (hle j)))).mp hzero
    exact sub_eq_zero.mp ((mul_eq_zero.mp (h i (Finset.mem_univ i))).resolve_left
      (ne_of_gt (hw i)))
  have hpLin : LinearIndependent ℝ p :=
    linearIndependent_of_affineIndependent_inner_const hp
      (ne_of_gt (real_inner_self_pos.mpr hne)) hinner
  refine ⟨Finset.univ.image p, ?_, ?_, ?_⟩
  · simpa using hpK
  · exact (Finset.card_image_le).trans (by simpa using hpLin.fintype_card_le_finrank)
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rw [← heq]
    exact (convex_convexHull ℝ (Set.range p)).sum_mem
      (fun i _ => (hw i).le) hsum (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)

theorem colorful_caratheodory [FiniteDimensional ℝ E]
    {ι J : Type*} [Fintype ι] [Nonempty ι] [Fintype J] [Nonempty J]
    (v : ι → J → E) (hcard : Module.finrank ℝ E < Fintype.card ι)
    (hcolor : ∀ i, (0 : E) ∈ convexHull ℝ (Set.range (v i))) :
    ∃ f : ι → J, (0 : E) ∈ convexHull ℝ (Set.range (fun i => v i (f i))) := by
  classical
  let K : (ι → J) → Set E := fun f => convexHull ℝ (Set.range (fun i => v i (f i)))
  let U : Set E := ⋃ f : ι → J, K f
  have hcompact : IsCompact U :=
    isCompact_iUnion (fun f => (Set.finite_range _).isCompact_convexHull ℝ)
  have hnonempty : U.Nonempty := by
    let f : ι → J := fun _ => Classical.arbitrary J
    let i : ι := Classical.arbitrary ι
    exact ⟨v i (f i), Set.mem_iUnion.mpr
      ⟨f, subset_convexHull ℝ _ ⟨i, rfl⟩⟩⟩
  obtain ⟨x, hxU, hmin⟩ := hcompact.exists_isMinOn hnonempty continuous_norm.continuousOn
  obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hxU
  by_cases hxzero : x = 0
  · exact ⟨f, hxzero ▸ hxf⟩
  obtain ⟨t, ht, htcard, hxt⟩ := exists_small_support_of_min_norm hxf hxzero
    (fun y hy => hmin (Set.mem_iUnion.mpr ⟨f, hy⟩))
  choose index hindex using fun a : t => ht a.property
  have hmiss : ¬ Function.Surjective index := by
    intro hsurj
    have hle := Fintype.card_le_of_surjective index hsurj
    have : Fintype.card ι ≤ t.card := by simpa using hle
    omega
  simp only [Function.Surjective, not_forall, not_exists] at hmiss
  obtain ⟨k, hk⟩ := hmiss
  have hle : ∀ j, ⟪x, x⟫_ℝ ≤ ⟪x, v k j⟫_ℝ := by
    intro j
    let f' := Function.update f k j
    have ht' : (↑t : Set E) ⊆ Set.range (fun i => v i (f' i)) := by
      intro a ha
      refine ⟨index ⟨a, ha⟩, ?_⟩
      have hne : index ⟨a, ha⟩ ≠ k := fun heq => hk ⟨a, ha⟩ heq
      simpa [f', Function.update_of_ne hne] using hindex ⟨a, ha⟩
    have hxf' : x ∈ K f' := convexHull_mono ht' hxt
    apply inner_self_le_inner_of_min_norm (convex_convexHull ℝ _) hxf'
      (fun y hy => hmin (Set.mem_iUnion.mpr ⟨f', hy⟩))
    apply subset_convexHull ℝ _
    exact ⟨k, by simp [f']⟩
  have hhalf : convexHull ℝ (Set.range (v k)) ⊆
      {y : E | ⟪x, x⟫_ℝ ≤ ⟪x, y⟫_ℝ} := by
    apply convexHull_min
    · rintro y ⟨j, rfl⟩
      exact hle j
    · exact (convex_Ici (⟪x, x⟫_ℝ)).linear_preimage (innerSL ℝ x).toLinearMap
  have hbad := hhalf (hcolor k)
  have hpos := real_inner_self_pos.mpr hxzero
  simp only [Set.mem_setOf_eq, inner_zero_right] at hbad
  exact (not_le_of_gt hpos hbad).elim

end TverbergProof

open scoped BigOperators
open Set

namespace TverbergProof

theorem euclidean_sum_apply {ι κ : Type*} [Fintype κ]
    (s : Finset ι) (v : ι → EuclideanSpace ℝ κ) (a : κ) :
    (∑ i ∈ s, v i) a = ∑ i ∈ s, v i a := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, PiLp.add_apply, ih]

noncomputable def simplexCoefficient {k : ℕ} (j : Fin (k + 1)) (a : Fin k) : ℝ :=
  (if j = a.castSucc then 1 else 0) - (if j = Fin.last k then 1 else 0)

noncomputable def homogeneousPoint {d : ℕ} (p : EuclideanSpace ℝ (Fin d)) :
    Fin (d + 1) → ℝ := Fin.cases 1 p

noncomputable def tensorLift {k d : ℕ} (p : EuclideanSpace ℝ (Fin d))
    (j : Fin (k + 1)) : EuclideanSpace ℝ (Fin k × Fin (d + 1)) :=
  WithLp.toLp 2 (fun a => simplexCoefficient j a.1 * homogeneousPoint p a.2)

theorem sum_tensorLift {k d : ℕ} (p : EuclideanSpace ℝ (Fin d)) :
    ∑ j : Fin (k + 1), tensorLift (k := k) p j = 0 := by
  ext a
  simp [tensorLift, simplexCoefficient, euclidean_sum_apply, sub_mul,
    Finset.sum_sub_distrib]

theorem zero_mem_convexHull_tensorLift {k d : ℕ} (p : EuclideanSpace ℝ (Fin d)) :
    (0 : EuclideanSpace ℝ (Fin k × Fin (d + 1))) ∈
      convexHull ℝ (Set.range (tensorLift (k := k) p)) := by
  apply mem_convexHull_of_exists_fintype (fun _ : Fin (k + 1) => ((k + 1 : ℕ) : ℝ)⁻¹)
    (tensorLift p)
  · intro i
    positivity
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by positivity)
  · exact fun i => ⟨i, rfl⟩
  · rw [← Finset.smul_sum, sum_tensorLift, smul_zero]

theorem weights_of_mem_convexHull_range {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] {p : ι → E} {x : E}
    (hx : x ∈ convexHull ℝ (Set.range p)) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • p i = x := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨s, w, hw, hsum, heq⟩ := hx
  refine ⟨fun i => if i ∈ s then w i else 0, ?_, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs with hi
    · exact hw i hi
    · exact le_rfl
  · simpa using hsum
  · rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum] at heq
    simpa [ite_smul] using heq

theorem balanced_weights_of_tensor_zero {ι : Type*} [Fintype ι]
    {k d : ℕ} (p : ι → EuclideanSpace ℝ (Fin d)) (f : ι → Fin (k + 1))
    (w : ι → ℝ)
    (hzero : ∑ i, w i • tensorLift (p i) (f i) = 0) :
    (∀ j l : Fin (k + 1),
      ∑ i ∈ Finset.univ.filter (fun i => f i = j), w i =
      ∑ i ∈ Finset.univ.filter (fun i => f i = l), w i) ∧
    (∀ j l : Fin (k + 1),
      ∑ i ∈ Finset.univ.filter (fun i => f i = j), w i • p i =
      ∑ i ∈ Finset.univ.filter (fun i => f i = l), w i • p i) := by
  classical
  have hcoord (a : Fin k) (b : Fin (d + 1)) :
      ∑ i ∈ Finset.univ.filter (fun i => f i = a.castSucc),
          w i * homogeneousPoint (p i) b =
        ∑ i ∈ Finset.univ.filter (fun i => f i = Fin.last k),
          w i * homogeneousPoint (p i) b := by
    have h := congrArg (fun z : EuclideanSpace ℝ (Fin k × Fin (d + 1)) => z (a, b)) hzero
    simp only [euclidean_sum_apply, PiLp.smul_apply, tensorLift, PiLp.toLp_apply,
      simplexCoefficient, smul_eq_mul, PiLp.zero_apply] at h
    simpa [Finset.sum_filter, mul_sub, sub_mul, Finset.sum_sub_distrib,
      mul_ite, ite_mul, sub_eq_zero] using h
  have hmass (j : Fin (k + 1)) :
      ∑ i ∈ Finset.univ.filter (fun i => f i = j), w i =
        ∑ i ∈ Finset.univ.filter (fun i => f i = Fin.last k), w i := by
    refine Fin.lastCases rfl (fun a => ?_) j
    simpa [homogeneousPoint] using hcoord a 0
  have hmoment (j : Fin (k + 1)) :
      ∑ i ∈ Finset.univ.filter (fun i => f i = j), w i • p i =
        ∑ i ∈ Finset.univ.filter (fun i => f i = Fin.last k), w i • p i := by
    refine Fin.lastCases rfl (fun a => ?_) j
    ext b
    simpa [homogeneousPoint, euclidean_sum_apply, PiLp.smul_apply] using hcoord a b.succ
  exact ⟨fun j l => (hmass j).trans (hmass l).symm,
    fun j l => (hmoment j).trans (hmoment l).symm⟩

theorem exists_balanced_weights (k d : ℕ)
    (p : Fin (k * (d + 1) + 1) → EuclideanSpace ℝ (Fin d)) :
    ∃ (f : Fin (k * (d + 1) + 1) → Fin (k + 1))
      (w : Fin (k * (d + 1) + 1) → ℝ),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      (∀ j l : Fin (k + 1),
        ∑ i ∈ Finset.univ.filter (fun i => f i = j), w i =
        ∑ i ∈ Finset.univ.filter (fun i => f i = l), w i) ∧
      (∀ j l : Fin (k + 1),
        ∑ i ∈ Finset.univ.filter (fun i => f i = j), w i • p i =
        ∑ i ∈ Finset.univ.filter (fun i => f i = l), w i • p i) := by
  obtain ⟨f, hf⟩ := colorful_caratheodory
    (fun i => tensorLift (k := k) (p i)) (by simp) (fun i => zero_mem_convexHull_tensorLift (p i))
  obtain ⟨w, hw, hsum, heq⟩ := weights_of_mem_convexHull_range hf
  obtain ⟨hmass, hmoment⟩ := balanced_weights_of_tensor_zero p f w heq
  exact ⟨f, w, hw, hsum, hmass, hmoment⟩

end TverbergProof

open scoped BigOperators
open Set

namespace TverbergProof

theorem partition_of_balanced_weights
    {ι E : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq E]
    [AddCommGroup E] [Module ℝ E]
    (r : ℕ) (hr : 0 < r) (p : ι → E) (f : ι → Fin r) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hmass : ∀ j k : Fin r,
      ∑ i ∈ Finset.univ.filter (fun i => f i = j), w i =
        ∑ i ∈ Finset.univ.filter (fun i => f i = k), w i)
    (hmoment : ∀ j k : Fin r,
      ∑ i ∈ Finset.univ.filter (fun i => f i = j), w i • p i =
        ∑ i ∈ Finset.univ.filter (fun i => f i = k), w i • p i) :
    ∃ partition : Fin r → Finset ι,
      (∀ j, (partition j).Nonempty) ∧
      Finset.univ = Finset.biUnion Finset.univ partition ∧
      (∀ j k, j ≠ k → Disjoint (partition j) (partition k)) ∧
      (⋂ j, convexHull ℝ ((partition j).image p : Set E)).Nonempty := by
  classical
  let partition : Fin r → Finset ι := fun j => Finset.univ.filter (fun i => f i = j)
  have hpositive : ∃ i, 0 < w i := by
    by_contra! h
    have hnonpos : ∑ i, w i ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
    rw [hsum] at hnonpos
    norm_num at hnonpos
  obtain ⟨i₀, hi₀⟩ := hpositive
  let m : ℝ := ∑ i ∈ partition (f i₀), w i
  have hm : 0 < m := by
    apply lt_of_lt_of_le hi₀
    exact Finset.single_le_sum (fun i _ => hw i) (by simp [partition])
  have hmass' (j : Fin r) : ∑ i ∈ partition j, w i = m := hmass j (f i₀)
  let point : E := m⁻¹ • ∑ i ∈ partition (f i₀), w i • p i
  refine ⟨partition, ?_, ?_, ?_, point, ?_⟩
  · intro j
    by_contra h
    have hempty : partition j = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hzero : m = 0 := by simpa [hempty] using (hmass' j).symm
    exact (ne_of_gt hm) hzero
  · ext i
    simp [partition]
  · intro j k hjk
    apply Finset.disjoint_left.mpr
    intro i hij hik
    have hij' := (Finset.mem_filter.mp hij).2
    have hik' := (Finset.mem_filter.mp hik).2
    exact hjk (hij'.symm.trans hik')
  · apply Set.mem_iInter.mpr
    intro j
    have hweights : ∑ i ∈ partition j, w i / m = 1 := by
      rw [← Finset.sum_div, hmass' j, div_self (ne_of_gt hm)]
    have hbary : (∑ i ∈ partition j, (w i / m) • p i) ∈
        convexHull ℝ ((partition j).image p : Set E) := by
      apply (convex_convexHull ℝ _).sum_mem
        (fun i _ => div_nonneg (hw i) hm.le) hweights
      intro i hi
      apply subset_convexHull ℝ _
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have heq : (∑ i ∈ partition j, (w i / m) • p i) = point := by
      calc
        _ = m⁻¹ • ∑ i ∈ partition j, w i • p i := by
          simp only [Finset.smul_sum, smul_smul, div_eq_mul_inv, mul_comm]
        _ = point := by
          exact congrArg (fun v : E => m⁻¹ • v) (hmoment j (f i₀))
    exact heq ▸ hbary

end TverbergProof

theorem solution (r d : ℕ) (hr : 2 ≤ r) (hd : 1 ≤ d) :
    ∀ (pts : Fin ((r - 1) * (d + 1) + 1) → EuclideanSpace ℝ (Fin d)),
      ∃ (partition : Fin r → Finset (Fin ((r-1)*(d+1)+1))),
        (∀ i, (partition i).Nonempty) ∧
        Finset.univ = Finset.biUnion Finset.univ partition ∧
        (∀ i j, i ≠ j → Disjoint (partition i) (partition j)) ∧
        (⋂ i : Fin r, convexHull ℝ
          ((partition i).image pts : Set (EuclideanSpace ℝ (Fin d)))).Nonempty := by
  cases r with
  | zero => omega
  | succ k =>
      simp only [Nat.succ_sub_one]
      intro pts
      obtain ⟨f, w, hw, hsum, hmass, hmoment⟩ :=
        TverbergProof.exists_balanced_weights k d pts
      exact TverbergProof.partition_of_balanced_weights (k + 1) (by omega)
        pts f w hw hsum hmass hmoment

#check @solution
#print axioms solution
