-- Prove2me | solution 1 for sampled_row_column_energy_max_moment_from_row_and_column_bounds_of_sample_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T19:25:58.816284+00:00
-- url     : https://prove2.me/submissions/5ed9ac41-4c25-4f88-9c71-68bb2de6b263

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic

open MatrixCompletion

open scoped Classical BigOperators

private lemma bernoulliObservationWeight_nonneg
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  exact mul_nonneg (pow_nonneg hp _)
    (pow_nonneg (sub_nonneg.mpr hp_one) _)

private lemma bernoulliExpectation_mono
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    {F G : Finset (Fin n₁ × Fin n₂) → ℝ} :
    (∀ Omega, F Omega ≤ G Omega) →
    bernoulliExpectation p F ≤ bernoulliExpectation p G := by
  intro hFG
  unfold bernoulliExpectation
  apply Finset.sum_le_sum
  intro Omega _
  exact mul_le_mul_of_nonneg_left (hFG Omega)
    (bernoulliObservationWeight_nonneg hp hp_one Omega)

private lemma bernoulliExpectation_add
    {n₁ n₂ : ℕ} (p : ℝ)
    (F G : Finset (Fin n₁ × Fin n₂) → ℝ) :
    bernoulliExpectation p (fun Omega => F Omega + G Omega) =
      bernoulliExpectation p F + bernoulliExpectation p G := by
  unfold bernoulliExpectation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Omega _
  ring

private lemma sample_ratio_nonneg
    {n₁ n₂ m : ℕ} :
    0 ≤ ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
  exact div_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

private lemma sample_ratio_le_one
    {n₁ n₂ m : ℕ} :
    0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ≤ 1 := by
  intro hn₁ hn₂ hm
  have hden_pos : 0 < (n₁ : ℝ) * (n₂ : ℝ) :=
    mul_pos (Nat.cast_pos.mpr hn₁) (Nat.cast_pos.mpr hn₂)
  have hnum_le_den : (m : ℝ) ≤ (n₁ : ℝ) * (n₂ : ℝ) := by
    exact_mod_cast hm
  rw [div_le_iff₀ hden_pos]
  simpa using hnum_le_den

private lemma sampledRowEnergyMax_nonneg
    {n₁ n₂ : ℕ} (hn₁ : 0 < n₁)
    (Omega : Finset (Fin n₁ × Fin n₂)) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    0 ≤ sampledRowEnergyMax Omega X := by
  classical
  let i0 : Fin n₁ := ⟨0, hn₁⟩
  have hrow_nonneg :
      0 ≤ ∑ j : Fin n₂, if (i0, j) ∈ Omega then X i0 j ^ 2 else 0 := by
    apply Finset.sum_nonneg
    intro j _
    by_cases hmem : (i0, j) ∈ Omega
    · simp [hmem, sq_nonneg]
    · simp [hmem]
  have hle :
      (∑ j : Fin n₂, if (i0, j) ∈ Omega then X i0 j ^ 2 else 0) ≤
        ⨆ i : Fin n₁, ∑ j : Fin n₂,
          if (i, j) ∈ Omega then X i j ^ 2 else 0 := by
    exact le_ciSup
      (Finite.bddAbove_range
        (f := fun i : Fin n₁ =>
          ∑ j : Fin n₂, if (i, j) ∈ Omega then X i j ^ 2 else 0))
      i0
  exact le_trans hrow_nonneg hle

private lemma sampledColumnEnergyMax_nonneg
    {n₁ n₂ : ℕ} (hn₂ : 0 < n₂)
    (Omega : Finset (Fin n₁ × Fin n₂)) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    0 ≤ sampledColumnEnergyMax Omega X := by
  classical
  let j0 : Fin n₂ := ⟨0, hn₂⟩
  have hcol_nonneg :
      0 ≤ ∑ i : Fin n₁, if (i, j0) ∈ Omega then X i j0 ^ 2 else 0 := by
    apply Finset.sum_nonneg
    intro i _
    by_cases hmem : (i, j0) ∈ Omega
    · simp [hmem, sq_nonneg]
    · simp [hmem]
  have hle :
      (∑ i : Fin n₁, if (i, j0) ∈ Omega then X i j0 ^ 2 else 0) ≤
        ⨆ j : Fin n₂, ∑ i : Fin n₁,
          if (i, j) ∈ Omega then X i j ^ 2 else 0 := by
    exact le_ciSup
      (Finite.bddAbove_range
        (f := fun j : Fin n₂ =>
          ∑ i : Fin n₁, if (i, j) ∈ Omega then X i j ^ 2 else 0))
      j0
  exact le_trans hcol_nonneg hle

private lemma max_pow_le_sum_pow_of_nonneg
    {a b : ℝ} (q : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max a b ^ q ≤ a ^ q + b ^ q := by
  by_cases hab : a ≤ b
  · have hmax : max a b = b := max_eq_right hab
    rw [hmax]
    exact le_add_of_nonneg_left (pow_nonneg ha _)
  · have hba : b ≤ a := le_of_lt (lt_of_not_ge hab)
    have hmax : max a b = a := max_eq_left hba
    rw [hmax]
    exact le_add_of_nonneg_right (pow_nonneg hb _)

private lemma two_mul_pow_dominates_two
    {x : ℝ} {q : ℕ} (hq : 1 ≤ q) (hx : 0 ≤ x) :
    2 * x ^ q ≤ (2 * x) ^ q := by
  cases q with
  | zero => omega
  | succ q =>
      rw [mul_pow]
      have htwo_pow : (2 : ℝ) ≤ 2 ^ Nat.succ q := by
        rw [pow_succ]
        have hge : (1 : ℝ) ≤ 2 ^ q :=
          one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
        nlinarith
      exact mul_le_mul_of_nonneg_right htwo_pow (pow_nonneg hx _)

theorem solution
    (Crow Ccol : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n₁ n₂ : ℕ} (m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 1 ≤ q →
        0 < Crow → 0 < Ccol →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega => sampledRowEnergyMax Omega X ^ q) ≤
          (Crow * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega => sampledColumnEnergyMax Omega X ^ q) ≤
          (Ccol * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X)) ^ q) ≤
          (C * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q := by
  refine ⟨2 * max (max Crow Ccol) 1, ?_, ?_⟩
  · positivity
  intro n₁ n₂ m q X hn₁ hn₂ hm hq hCrow hCcol hrow hcol
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let n : ℝ := ↑(max n₁ n₂)
  let scale : ℝ := p * n * entrySupNorm X ^ 2
  have hp : 0 ≤ p := sample_ratio_nonneg
  have hp_one : p ≤ 1 := sample_ratio_le_one hn₁ hn₂ hm
  have hscale_nonneg : 0 ≤ scale := by
    have hn_nonneg : 0 ≤ n := Nat.cast_nonneg _
    have hentry_nonneg : 0 ≤ entrySupNorm X ^ 2 := sq_nonneg _
    exact mul_nonneg (mul_nonneg hp hn_nonneg) hentry_nonneg
  have hmax_moment :
      bernoulliExpectation p
          (fun Omega =>
            (max (sampledRowEnergyMax Omega X)
              (sampledColumnEnergyMax Omega X)) ^ q) ≤
        bernoulliExpectation p
          (fun Omega =>
            sampledRowEnergyMax Omega X ^ q +
              sampledColumnEnergyMax Omega X ^ q) := by
    apply bernoulliExpectation_mono hp hp_one
    intro Omega
    exact max_pow_le_sum_pow_of_nonneg q
      (sampledRowEnergyMax_nonneg hn₁ Omega X)
      (sampledColumnEnergyMax_nonneg hn₂ Omega X)
  have hsum_moment :
      bernoulliExpectation p
          (fun Omega =>
            sampledRowEnergyMax Omega X ^ q +
              sampledColumnEnergyMax Omega X ^ q) ≤
        (Crow * p * n * entrySupNorm X ^ 2) ^ q +
          (Ccol * p * n * entrySupNorm X ^ 2) ^ q := by
    rw [bernoulliExpectation_add]
    exact add_le_add hrow hcol
  let Cmax : ℝ := max (max Crow Ccol) 1
  have hCrow_le : Crow ≤ Cmax := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCcol_le : Ccol ≤ Cmax := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCmax_pos : 0 < Cmax := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hCmax_nonneg : 0 ≤ Cmax := le_of_lt hCmax_pos
  have hrow_scalar :
      (Crow * p * n * entrySupNorm X ^ 2) ^ q ≤
        (Cmax * scale) ^ q := by
    have hbase :
        Crow * p * n * entrySupNorm X ^ 2 ≤ Cmax * scale := by
      dsimp [scale]
      have hscale0 : 0 ≤ p * n * entrySupNorm X ^ 2 := hscale_nonneg
      nlinarith [mul_le_mul_of_nonneg_right hCrow_le hscale0]
    have hleft_nonneg :
        0 ≤ Crow * p * n * entrySupNorm X ^ 2 := by
      have hn_nonneg : 0 ≤ n := Nat.cast_nonneg _
      exact mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hCrow) hp) hn_nonneg)
        (sq_nonneg _)
    exact pow_le_pow_left₀ hleft_nonneg hbase q
  have hcol_scalar :
      (Ccol * p * n * entrySupNorm X ^ 2) ^ q ≤
        (Cmax * scale) ^ q := by
    have hbase :
        Ccol * p * n * entrySupNorm X ^ 2 ≤ Cmax * scale := by
      dsimp [scale]
      have hscale0 : 0 ≤ p * n * entrySupNorm X ^ 2 := hscale_nonneg
      nlinarith [mul_le_mul_of_nonneg_right hCcol_le hscale0]
    have hleft_nonneg :
        0 ≤ Ccol * p * n * entrySupNorm X ^ 2 := by
      have hn_nonneg : 0 ≤ n := Nat.cast_nonneg _
      exact mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hCcol) hp) hn_nonneg)
        (sq_nonneg _)
    exact pow_le_pow_left₀ hleft_nonneg hbase q
  have hscalar :
      (Crow * p * n * entrySupNorm X ^ 2) ^ q +
          (Ccol * p * n * entrySupNorm X ^ 2) ^ q ≤
        (2 * max (max Crow Ccol) 1 * p * n * entrySupNorm X ^ 2) ^ q := by
    have htwo :
        (Crow * p * n * entrySupNorm X ^ 2) ^ q +
            (Ccol * p * n * entrySupNorm X ^ 2) ^ q ≤
          2 * ((Cmax * scale) ^ q) := by
      nlinarith
    have hdom :
        2 * ((Cmax * scale) ^ q) ≤
          (2 * (Cmax * scale)) ^ q := by
      exact two_mul_pow_dominates_two hq
        (mul_nonneg hCmax_nonneg hscale_nonneg)
    have hrewrite :
        (2 * (Cmax * scale)) ^ q =
          (2 * max (max Crow Ccol) 1 * p * n * entrySupNorm X ^ 2) ^ q := by
      dsimp [scale]
      ring
    simpa [hrewrite] using le_trans htwo hdom
  have hmain := le_trans hmax_moment (le_trans hsum_moment hscalar)
  simpa [p, n, scale, mul_assoc, mul_left_comm, mul_comm] using hmain
