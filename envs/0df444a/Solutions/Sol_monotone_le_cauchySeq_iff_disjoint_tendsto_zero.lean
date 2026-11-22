-- Prove2me | solution 1 for monotone_le_cauchySeq_iff_disjoint_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:19:15.408806+00:00
-- url     : https://prove2.me/submissions/121eb1a7-8a18-4df5-9180-59abaddc57d1

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Nakano
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_MeyerNieberg
public import Theorems.Thm_exists_disjoint_sequences_approx_of_monotone_le
public import Theorems.Thm_OrderConvergesTo_smul
public import Theorems.Thm_add_eq_sup_of_isVLDisjoint_of_nonneg
public import Theorems.Thm_inf_eq_zero_of_isVLDisjoint
public import Theorems.Thm_inf_le_inf_add_inf_of_nonneg
public import Theorems.Thm_isVLDisjoint_of_inf_eq_zero

section
@[expose] public section
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
section Disjointification
variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [VectorLattice E]
end Disjointification
section NormCriterion
variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [NormedVectorLattice E]
omit [NormedVectorLattice E] in
/-- One direction of the interval criterion: Cauchy partial sums force disjoint
sequences in the interval to converge to zero in norm. -/
private theorem disjoint_tendsto_zero_of_monotone_le_cauchySeq {x : E}
    (hx : 0 ≤ x)
    (hcauchy : ∀ {u : ℕ → E}, (∀ n, 0 ≤ u n) → Monotone u →
      (∀ n, u n ≤ x) → CauchySeq u)
    {u : ℕ → E} (hu_interval : ∀ n, u n ∈ Set.Icc (0 : E) x)
    (hu_disj : Pairwise fun n m => IsVLDisjoint (u n) (u m)) :
    Filter.Tendsto u Filter.atTop (nhds 0) := by
  let v : ℕ → E := fun m => ∑ k ∈ Finset.range m, u k
  have hv_nn : ∀ m, 0 ≤ v m := fun m =>
    Finset.sum_nonneg (fun k _ => (hu_interval k).1)
  have hv_mono : Monotone v := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    simp only [v, Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hu_interval n).1
  have key : ∀ m k, m ≤ k → v m ⊓ u k = 0 := by
    intro m
    induction m with
    | zero =>
        intro k _
        simpa [v] using (inf_eq_left.mpr (hu_interval k).1 : (0 : E) ⊓ u k = 0)
    | succ n ih =>
        intro k hk
        have h1 : v n ⊓ u k = 0 := ih k (by omega)
        have h2 : u n ⊓ u k = 0 :=
          inf_eq_zero_of_isVLDisjoint (hu_interval n).1 (hu_interval k).1
            (hu_disj (by omega))
        have heq : v (n + 1) = v n + u n := by
          simp [v, Finset.sum_range_succ]
        refine le_antisymm ?_
          (le_inf (by rw [heq]; exact add_nonneg (hv_nn n) (hu_interval n).1)
            (hu_interval k).1)
        rw [heq, inf_comm]
        calc u k ⊓ (v n + u n)
            ≤ u k ⊓ v n + u k ⊓ u n :=
              inf_le_inf_add_inf_of_nonneg (x := u k) (v n) (u n)
                (hu_interval k).1 (hv_nn n) (hu_interval n).1
          _ = 0 := by rw [inf_comm, h1, inf_comm, h2, add_zero]
  have hv_le : ∀ m, v m ≤ x := by
    intro m
    induction m with
    | zero => simpa [v] using hx
    | succ n ih =>
        have hdisj : IsVLDisjoint (v n) (u n) :=
          isVLDisjoint_of_inf_eq_zero (key n n (le_refl n))
        have heq : v (n + 1) = v n + u n := by
          simp [v, Finset.sum_range_succ]
        have hsup : v n + u n = v n ⊔ u n :=
          add_eq_sup_of_isVLDisjoint_of_nonneg (hv_nn n) (hu_interval n).1 hdisj
        rw [heq, hsup]
        exact sup_le ih (hu_interval n).2
  have hv_cauchy : CauchySeq v := hcauchy hv_nn hv_mono hv_le
  rw [Metric.cauchySeq_iff] at hv_cauchy
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := hv_cauchy ε hε
  refine Filter.eventually_atTop.mpr ⟨N, fun m hm => ?_⟩
  have hdist : dist (v (m + 1)) (v m) < ε := hN (m + 1) (by omega) m hm
  have heq : v (m + 1) - v m = u m := by
    simp [v, Finset.sum_range_succ]
  rw [dist_zero_right]
  rw [dist_eq_norm, heq] at hdist
  exact hdist
private theorem monotone_le_cauchySeq_of_disjoint_tendsto_zero {x : E}
    (hx : 0 ≤ x)
    (hdisj : ∀ {u : ℕ → E}, (∀ n, u n ∈ Set.Icc (0 : E) x) →
      Pairwise (fun n m => IsVLDisjoint (u n) (u m)) →
      Filter.Tendsto u Filter.atTop (nhds 0))
    {u : ℕ → E} (h0 : ∀ n, 0 ≤ u n) (hmono : Monotone u)
    (hle : ∀ n, u n ≤ x) :
    CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  by_contra hbad
  push Not at hbad
  let next : ℕ → ℕ := fun N => (hbad N).choose
  have hnext : ∀ N, N ≤ next N ∧ ε ≤ dist (u (next N)) (u N) :=
    fun N => (hbad N).choose_spec
  let φ : ℕ → ℕ := fun n => Nat.rec 0 (fun _ N => next N) n
  have hφ_succ : ∀ n, φ n < φ (n + 1) := by
    intro n
    have hleφ : φ n ≤ φ (n + 1) := (hnext (φ n)).1
    refine lt_of_le_of_ne hleφ ?_
    intro heq
    have hdist : ε ≤ dist (u (φ (n + 1))) (u (φ n)) := by
      simpa [φ] using (hnext (φ n)).2
    rw [heq, dist_self] at hdist
    linarith
  have hφ_strict : StrictMono φ := strictMono_nat_of_lt_succ hφ_succ
  let z : ℕ → E := fun n => u (φ n)
  have hz0 : ∀ n, 0 ≤ z n := fun n => h0 (φ n)
  have hz_mono : Monotone z := fun m n hmn => hmono (hφ_strict.monotone hmn)
  have hz_le : ∀ n, z n ≤ x := fun n => hle (φ n)
  have hcoeff_tend :
      Filter.Tendsto (fun k : ℕ => ‖((2 : ℝ) / ((k : ℝ) + 3)) • x‖)
        Filter.atTop (nhds 0) := by
    have hone :
        Filter.Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 3)) Filter.atTop
          (nhds 0) := by
      have hbase :
          Filter.Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) Filter.atTop
            (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      convert hbase.comp (Filter.tendsto_add_atTop_nat 2) using 1
      ext k
      simp
      ring
    have htwo :
        Filter.Tendsto (fun k : ℕ => (2 : ℝ) / ((k : ℝ) + 3)) Filter.atTop
          (nhds 0) := by
      simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hone)
    have hvec :
        Filter.Tendsto (fun k : ℕ => ((2 : ℝ) / ((k : ℝ) + 3)) • x)
          Filter.atTop (nhds ((0 : ℝ) • x)) :=
      htwo.smul (show Filter.Tendsto (fun _ : ℕ => x) Filter.atTop (nhds x) from
        tendsto_const_nhds)
    simpa using hvec.norm
  have herr_event := Metric.tendsto_nhds.mp hcoeff_tend (ε / 2) (by linarith)
  rw [Filter.eventually_atTop] at herr_event
  obtain ⟨K, hK⟩ := herr_event
  let k : ℕ := K + 1
  have hkpos : 0 < k := by simp [k]
  have herr : ‖((2 : ℝ) / ((k : ℝ) + 3)) • x‖ < ε / 2 := by
    have hk := hK k (by simp [k])
    rw [Real.dist_eq] at hk
    simpa [abs_of_nonneg (norm_nonneg _)] using hk
  obtain ⟨y, hy_disj, hy_interval, hy_approx⟩ :=
    exists_disjoint_sequences_approx_of_monotone_le hz0 hz_mono hz_le hkpos
  have hy_tend : ∀ i : Fin k, Filter.Tendsto (y i) Filter.atTop (nhds 0) :=
    fun i => hdisj (hy_interval i) (hy_disj i)
  have hsum_tend :
      Filter.Tendsto (fun n => ∑ i : Fin k, y i n) Filter.atTop (nhds 0) := by
    have hsum :
        Filter.Tendsto (fun n => ∑ i : Fin k, y i n) Filter.atTop
          (nhds (∑ i : Fin k, (0 : E))) :=
      tendsto_finsetSum Finset.univ (fun i _ => hy_tend i)
    simpa using hsum
  have hsum_event := Metric.tendsto_nhds.mp hsum_tend (ε / 2) (by linarith)
  rw [Filter.eventually_atTop] at hsum_event
  obtain ⟨N, hN⟩ := hsum_event
  have hsmall_sum : dist (∑ i : Fin k, y i N) 0 < ε / 2 := hN N (le_refl N)
  rw [dist_zero_right] at hsmall_sum
  have hlower : ε ≤ ‖z (N + 1) - z N‖ := by
    have hdist : ε ≤ dist (u (φ (N + 1))) (u (φ N)) := by
      simpa [φ] using (hnext (φ N)).2
    rwa [dist_eq_norm] at hdist
  have hd_nonneg : 0 ≤ z (N + 1) - z N :=
    sub_nonneg.mpr (hz_mono (Nat.le_succ N))
  have hsum_nonneg : 0 ≤ ∑ i : Fin k, y i N :=
    Finset.sum_nonneg fun i _ => (hy_interval i N).1
  have hcoeff_nonneg : 0 ≤ (2 : ℝ) / ((k : ℝ) + 3) := by positivity
  have hrhs_nonneg : 0 ≤
      (∑ i : Fin k, y i N) + ((2 : ℝ) / ((k : ℝ) + 3)) • x :=
    add_nonneg hsum_nonneg (smul_nonneg hcoeff_nonneg hx)
  have hnorm_le :
      ‖z (N + 1) - z N‖ ≤
        ‖(∑ i : Fin k, y i N) + ((2 : ℝ) / ((k : ℝ) + 3)) • x‖ := by
    rw [← norm_abs_eq_norm (z (N + 1) - z N),
      ← norm_abs_eq_norm ((∑ i : Fin k, y i N) + ((2 : ℝ) / ((k : ℝ) + 3)) • x)]
    exact norm_le_norm_of_abs_le_abs (by
      simpa [abs_of_nonneg hd_nonneg, abs_of_nonneg hrhs_nonneg] using (hy_approx N).2)
  have hnorm_add :
      ‖(∑ i : Fin k, y i N) + ((2 : ℝ) / ((k : ℝ) + 3)) • x‖ <
        ε := by
    have htri :
        ‖(∑ i : Fin k, y i N) + ((2 : ℝ) / ((k : ℝ) + 3)) • x‖ ≤
          ‖∑ i : Fin k, y i N‖ + ‖((2 : ℝ) / ((k : ℝ) + 3)) • x‖ :=
      norm_add_le _ _
    linarith
  linarith
end NormCriterion
namespace BanachLattice
variable [BanachLattice X]
end BanachLattice
end
end

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [NormedVectorLattice E]
theorem _root_.solution {x : E} (hx : 0 ≤ x) :
    (∀ {u : ℕ → E}, (∀ n, 0 ≤ u n) → Monotone u → (∀ n, u n ≤ x) →
      CauchySeq u) ↔
    (∀ {u : ℕ → E}, (∀ n, u n ∈ Set.Icc (0 : E) x) →
      Pairwise (fun n m => IsVLDisjoint (u n) (u m)) →
      Filter.Tendsto u Filter.atTop (nhds 0)) := by
  exact ⟨disjoint_tendsto_zero_of_monotone_le_cauchySeq hx,
    monotone_le_cauchySeq_of_disjoint_tendsto_zero hx⟩
