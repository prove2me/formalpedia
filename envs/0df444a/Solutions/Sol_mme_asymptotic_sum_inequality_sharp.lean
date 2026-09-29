-- Prove2me | solution 1 for mme_asymptotic_sum_inequality_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:29:52.840305+00:00
-- url     : https://prove2.me/submissions/66a530a5-8bb8-406e-b52d-1455ce0cde20

import Definitions.Def_mme_tensor_bridge

open MME BigOperators

universe u

namespace MME

private theorem MMData.sum_inequality_sharp
    {R : Type u} [CommSemiring R] (P : StrassenPreorder R)
    (D : MMData R P) {iota : Type*} [Fintype iota]
    (n m p : iota → ℕ)
    (hn : ∀ i, 1 ≤ n i) (hm : ∀ i, 1 ≤ m i) (hp : ∀ i, 1 ≤ p i) :
    ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ (D.omegaAbs / 3) ≤
      StrassenPreorder.asymptoticRank P
        (∑ i, D.MMel (n i) (m i) (p i)) := by
  let rankBound := StrassenPreorder.asymptoticRank P
    (∑ i, D.MMel (n i) (m i) (p i))
  have hspec : ∀ phi : AsymptoticSpectrumPoint R P,
      ∑ i, phi (D.MMel (n i) (m i) (p i)) ≤ rankBound := by
    intro phi
    have h_le_AR := StrassenPreorder.eval_le_asymptoticRank P
      (∑ i, D.MMel (n i) (m i) (p i)) phi
    rwa [map_sum] at h_le_AR
  have htheta : ∀ phi : AsymptoticSpectrumPoint R P,
      ∑ i, (n i : ℝ) ^ D.θ₁ phi * (m i : ℝ) ^ D.θ₂ phi *
        (p i : ℝ) ^ D.θ₃ phi ≤ rankBound := by
    intro phi
    rw [show (∑ i, (n i : ℝ) ^ D.θ₁ phi * (m i : ℝ) ^ D.θ₂ phi *
          (p i : ℝ) ^ D.θ₃ phi) =
        ∑ i, phi (D.MMel (n i) (m i) (p i)) from
      Finset.sum_congr rfl fun i _ =>
        (D.MM_eval phi (hn i) (hm i) (hp i)).symm]
    exact hspec phi
  have hn_pos : ∀ i, (0 : ℝ) < (n i : ℝ) := fun i => by
    exact_mod_cast (Nat.zero_lt_of_lt (hn i))
  have hm_pos : ∀ i, (0 : ℝ) < (m i : ℝ) := fun i => by
    exact_mod_cast (Nat.zero_lt_of_lt (hm i))
  have hp_pos : ∀ i, (0 : ℝ) < (p i : ℝ) := fun i => by
    exact_mod_cast (Nat.zero_lt_of_lt (hp i))
  set F : ℝ × ℝ × ℝ → ℝ :=
    fun v => ∑ i, (n i : ℝ) ^ v.1 * (m i : ℝ) ^ v.2.1 *
      (p i : ℝ) ^ v.2.2 with hF
  have hF_convex : ConvexOn ℝ Set.univ F :=
    sum_rpow_convex (fun i => (n i : ℝ)) (fun i => (m i : ℝ))
      (fun i => (p i : ℝ)) hn_pos hm_pos hp_pos
  have hF_perm : ∀ phi : AsymptoticSpectrumPoint R P,
      ∀ sigma ∈ ({Equiv.refl _, cyclicPerm3, cyclicPerm3 * cyclicPerm3} :
          Set (Equiv.Perm (Fin 3))),
        F (permuteTriple sigma (D.θ₁ phi, D.θ₂ phi, D.θ₃ phi)) ≤
          rankBound := by
    intro phi sigma hsigma
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsigma
    obtain ⟨phi', hphi'⟩ := D.cyclic phi
    obtain ⟨phi'', hphi''⟩ := D.cyclic phi'
    obtain ⟨k1, k2, k3⟩ := D.theta_cyclic hphi'
    obtain ⟨l1, l2, l3⟩ := D.theta_cyclic hphi''
    rcases hsigma with h_id | h_c | h_c2
    · subst h_id
      have h_pt :
          permuteTriple (Equiv.refl _) (D.θ₁ phi, D.θ₂ phi, D.θ₃ phi) =
            (D.θ₁ phi, D.θ₂ phi, D.θ₃ phi) := rfl
      rw [h_pt]
      exact htheta phi
    · subst h_c
      have h_pt :
          permuteTriple cyclicPerm3 (D.θ₁ phi, D.θ₂ phi, D.θ₃ phi) =
            (D.θ₃ phi, D.θ₁ phi, D.θ₂ phi) := rfl
      rw [h_pt]
      have e1 : D.θ₁ phi'' = D.θ₃ phi := by rw [l1, k2]
      have e2 : D.θ₂ phi'' = D.θ₁ phi := by rw [l2, k3]
      have e3 : D.θ₃ phi'' = D.θ₂ phi := by rw [l3, k1]
      have h := htheta phi''
      rw [e1, e2, e3] at h
      exact h
    · subst h_c2
      have h_pt :
          permuteTriple (cyclicPerm3 * cyclicPerm3)
              (D.θ₁ phi, D.θ₂ phi, D.θ₃ phi) =
            (D.θ₂ phi, D.θ₃ phi, D.θ₁ phi) := rfl
      rw [h_pt]
      have e1 : D.θ₁ phi' = D.θ₂ phi := k1
      have e2 : D.θ₂ phi' = D.θ₃ phi := k2
      have e3 : D.θ₃ phi' = D.θ₁ phi := k3
      have h := htheta phi'
      rw [e1, e2, e3] at h
      exact h
  have h_avg : ∀ phi : AsymptoticSpectrumPoint R P,
      F ((D.θ₁ phi + D.θ₂ phi + D.θ₃ phi) / 3,
         (D.θ₁ phi + D.θ₂ phi + D.θ₃ phi) / 3,
         (D.θ₁ phi + D.θ₂ phi + D.θ₃ phi) / 3) ≤
        rankBound := fun phi =>
    jensen_S3_convex hF_convex (D.θ₁ phi, D.θ₂ phi, D.θ₃ phi)
      rankBound (hF_perm phi)
  set S : AsymptoticSpectrumPoint R P → ℝ :=
    fun phi => D.θ₁ phi + D.θ₂ phi + D.θ₃ phi with hS_def
  haveI : Nonempty (AsymptoticSpectrumPoint R P) := mme_spectrum_nonempty P
  have h_compact :
      IsCompact (Set.univ : Set (AsymptoticSpectrumPoint R P)) := isCompact_univ
  obtain ⟨phi_max, -, hmax⟩ :=
    h_compact.exists_isMaxOn Set.univ_nonempty
      D.continuous_θsum.continuousOn
  have h_supS : D.omegaAbs = S phi_max := by
    apply le_antisymm
    · refine ciSup_le ?_
      intro phi
      exact hmax (Set.mem_univ phi)
    · exact le_ciSup (f := S)
        ⟨S phi_max, fun y ⟨phi, hphi⟩ => hphi ▸ hmax (Set.mem_univ phi)⟩ phi_max
  rw [h_supS]
  have h_at_max := h_avg phi_max
  have h_eq : ∀ i, ((n i * m i * p i : ℕ) : ℝ) ^ (S phi_max / 3) =
      (n i : ℝ) ^ (S phi_max / 3) * (m i : ℝ) ^ (S phi_max / 3) *
        (p i : ℝ) ^ (S phi_max / 3) := by
    intro i
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (le_of_lt (hn_pos i)) (le_of_lt (hm_pos i))]
  calc
    ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ (S phi_max / 3) =
        ∑ i, (n i : ℝ) ^ (S phi_max / 3) *
          (m i : ℝ) ^ (S phi_max / 3) *
          (p i : ℝ) ^ (S phi_max / 3) :=
      Finset.sum_congr rfl fun i _ => h_eq i
    _ = F (S phi_max / 3, S phi_max / 3, S phi_max / 3) := rfl
    _ ≤ rankBound := h_at_max

private theorem sum_inequality_sharp_pos
    {K : Type u} [Field K] {k : ℕ}
    (n m p : Fin k → ℕ)
    (hn : ∀ i, 1 ≤ n i) (hm : ∀ i, 1 ≤ m i) (hp : ∀ i, 1 ≤ p i) :
    ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ (matMulExp_strassen K / 3) ≤
      tensorAsymptoticRank
        (TensorObj.bigAdd (fun i => MMObj K (n i) (m i) (p i))) := by
  have h := (mmTensorData K).sum_inequality_sharp
    (tensorPreorder K) n m p hn hm hp
  rw [bridge_omega] at h
  change ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^
      (matMulExp_strassen K / 3) ≤
    StrassenPreorder.asymptoticRank (tensorPreorder K)
      (∑ i, MMq K (n i) (m i) (p i)) at h
  rw [bridge_asymptoticRank] at h
  exact h

theorem asymptotic_sum_inequality_sharp_internal
    {K : Type u} [Field K] {k : ℕ} (n m p : Fin k → ℕ) :
    ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^
        (matMulExp_strassen K / 3) ≤
      tensorAsymptoticRank
        (TensorObj.bigAdd (fun i => MMObj K (n i) (m i) (p i))) := by
  classical
  set S : Finset (Fin k) :=
    Finset.univ.filter (fun i => 1 ≤ n i ∧ 1 ≤ m i ∧ 1 ≤ p i) with hS
  set e : Fin S.card ≃ {x // x ∈ S} := (S.equivFin).symm with he
  have hmemS : ∀ x : {x // x ∈ S},
      1 ≤ n x.1 ∧ 1 ≤ m x.1 ∧ 1 ≤ p x.1 := by
    intro x
    have hx : x.1 ∈ Finset.univ.filter
        (fun i => 1 ≤ n i ∧ 1 ≤ m i ∧ 1 ≤ p i) := hS ▸ x.2
    exact (Finset.mem_filter.mp hx).2
  have hn' : ∀ j : Fin S.card, 1 ≤ n (e j).1 := fun j => (hmemS (e j)).1
  have hm' : ∀ j : Fin S.card, 1 ≤ m (e j).1 := fun j => (hmemS (e j)).2.1
  have hp' : ∀ j : Fin S.card, 1 ≤ p (e j).1 := fun j => (hmemS (e j)).2.2
  have hsum_eq :
      (∑ j : Fin S.card, MMq K (n (e j).1) (m (e j).1) (p (e j).1)) =
        ∑ i, MMq K (n i) (m i) (p i) := by
    rw [show (∑ j : Fin S.card,
          MMq K (n (e j).1) (m (e j).1) (p (e j).1)) =
        ∑ x : {x // x ∈ S}, MMq K (n x.1) (m x.1) (p x.1) from
      Equiv.sum_comp e (fun x => MMq K (n x.1) (m x.1) (p x.1))]
    rw [Finset.sum_coe_sort S (fun i => MMq K (n i) (m i) (p i))]
    refine Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => ?_)
    rw [hS, Finset.mem_filter] at hi
    exact MMq_eq_zero_of_not_pos
      (fun hpos => hi ⟨Finset.mem_univ i, hpos⟩)
  have hAR_eq :
      tensorAsymptoticRank
          (TensorObj.bigAdd (fun j =>
            MMObj K (n (e j).1) (m (e j).1) (p (e j).1))) =
        tensorAsymptoticRank
          (TensorObj.bigAdd (fun i => MMObj K (n i) (m i) (p i))) := by
    rw [← bridge_asymptoticRank
      (fun j => n (e j).1) (fun j => m (e j).1) (fun j => p (e j).1),
      hsum_eq, bridge_asymptoticRank n m p]
  have hpos := sum_inequality_sharp_pos (K := K)
    (fun j => n (e j).1) (fun j => m (e j).1) (fun j => p (e j).1)
    hn' hm' hp'
  have hexp_ne : matMulExp_strassen K / 3 ≠ 0 := by
    have := matMulExp_strassen_pos (K := K)
    positivity
  have hreal_eq :
      (∑ j : Fin S.card,
        ((n (e j).1 * m (e j).1 * p (e j).1 : ℕ) : ℝ) ^
          (matMulExp_strassen K / 3)) =
        ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^
          (matMulExp_strassen K / 3) := by
    rw [show (∑ j : Fin S.card,
          ((n (e j).1 * m (e j).1 * p (e j).1 : ℕ) : ℝ) ^
            (matMulExp_strassen K / 3)) =
        ∑ x : {x // x ∈ S},
          ((n x.1 * m x.1 * p x.1 : ℕ) : ℝ) ^
            (matMulExp_strassen K / 3) from
      Equiv.sum_comp e (fun x =>
        ((n x.1 * m x.1 * p x.1 : ℕ) : ℝ) ^
          (matMulExp_strassen K / 3))]
    rw [Finset.sum_coe_sort S (fun i =>
      ((n i * m i * p i : ℕ) : ℝ) ^ (matMulExp_strassen K / 3))]
    refine Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => ?_)
    rw [hS, Finset.mem_filter] at hi
    have hnp : ¬ (1 ≤ n i ∧ 1 ≤ m i ∧ 1 ≤ p i) :=
      fun hpos => hi ⟨Finset.mem_univ i, hpos⟩
    have hzero : n i * m i * p i = 0 := by
      rcases (by omega : n i = 0 ∨ m i = 0 ∨ p i = 0) with h0 | h0 | h0 <;>
        simp [h0]
    rw [hzero, Nat.cast_zero, Real.zero_rpow hexp_ne]
  rw [← hreal_eq, ← hAR_eq]
  exact hpos

end MME

theorem solution
    {K : Type u} [Field K] {k : ℕ} (n m p : Fin k → ℕ) :
    ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^
        (MME.matMulExp_strassen K / 3) ≤
      MME.tensorAsymptoticRank
        (MME.TensorObj.bigAdd (fun i => MME.MMObj K (n i) (m i) (p i))) :=
  MME.asymptotic_sum_inequality_sharp_internal n m p
