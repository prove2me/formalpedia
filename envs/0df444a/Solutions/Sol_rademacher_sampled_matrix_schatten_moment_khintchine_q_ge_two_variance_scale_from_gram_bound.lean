-- Prove2me | solution 1 for rademacher_sampled_matrix_schatten_moment_khintchine_q_ge_two_variance_scale_from_gram_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-23T20:44:57.053107+00:00
-- url     : https://prove2.me/submissions/61285ab6-d900-4ad3-b22a-8daed274e253

import Definitions.Def_matrix_completion_gram_schatten
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open MatrixCompletion

private lemma sample_ratio_nonneg
    {n₁ n₂ m : ℕ} :
    0 ≤ ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
  exact div_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

private lemma rademacherSampledVarianceScale_nonneg_of_nonneg
    {n₁ n₂ : ℕ} (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (hp : 0 ≤ p) :
    0 ≤ rademacherSampledVarianceScale Omega p X := by
  unfold rademacherSampledVarianceScale
  exact mul_nonneg (inv_nonneg.mpr hp) (Real.sqrt_nonneg _)

private lemma sampledRowGramSchatten_nonneg_of_nonneg
    {n₁ n₂ : ℕ} (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (q : ℝ) (hp : 0 ≤ p) :
    0 ≤ sampledRowGramSchatten Omega p X q := by
  classical
  unfold sampledRowGramSchatten
  apply Real.rpow_nonneg
  apply Finset.sum_nonneg
  intro i _
  apply Real.rpow_nonneg
  exact mul_nonneg (inv_nonneg.mpr hp) (Real.sqrt_nonneg _)

private lemma sampledColumnGramSchatten_nonneg_of_nonneg
    {n₁ n₂ : ℕ} (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (q : ℝ) (hp : 0 ≤ p) :
    0 ≤ sampledColumnGramSchatten Omega p X q := by
  classical
  unfold sampledColumnGramSchatten
  apply Real.rpow_nonneg
  apply Finset.sum_nonneg
  intro j _
  apply Real.rpow_nonneg
  exact mul_nonneg (inv_nonneg.mpr hp) (Real.sqrt_nonneg _)

private lemma sampledGramMax_nonneg_of_nonneg
    {n₁ n₂ : ℕ} (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (q : ℝ) (hp : 0 ≤ p) :
    0 ≤ max (sampledRowGramSchatten Omega p X q)
        (sampledColumnGramSchatten Omega p X q) := by
  exact le_trans
    (sampledRowGramSchatten_nonneg_of_nonneg Omega p X q hp)
    (le_max_left _ _)

/-- Direct proof of the formal constant-absorption child in the `q ≥ 2`
Khintchine branch. -/
theorem solution
    (Ccore : ℝ) :
    0 < Ccore →
    (∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ)
        (Omega : Finset (Fin n₁ × Fin n₂))
        (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        2 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        rademacherExpectation
            (fun eps =>
              schattenNorm (q : ℝ)
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (Ccore * Real.sqrt (q : ℝ) *
            max (sampledRowGramSchatten Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X (q : ℝ))
                (sampledColumnGramSchatten Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X (q : ℝ))) ^ q) →
    (∀ {n₁ n₂ : ℕ}
        (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ)
        (X : Matrix (Fin n₁) (Fin n₂) ℝ)
        (q β : ℝ), 0 ≤ p → 2 < β → 1 ≤ q →
        q ≥ β * Real.log (↑(max n₁ n₂)) →
        max (sampledRowGramSchatten Omega p X q)
            (sampledColumnGramSchatten Omega p X q) ≤
          Real.exp (1 / 2) * rademacherSampledVarianceScale Omega p X) →
    ∃ Ckh : ℝ, 0 < Ckh ∧
      ∀ Cbig : ℝ, Ckh ≤ Cbig →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ)
        (Omega : Finset (Fin n₁ × Fin n₂))
        (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        2 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        rademacherExpectation
            (fun eps =>
              schattenNorm (q : ℝ)
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (Cbig * Real.sqrt (q : ℝ) *
            rademacherSampledVarianceScale Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q := by
  intro hCcore hCore hGram
  refine ⟨max 1 (Ccore * Real.exp (1 / 2)), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  intro Cbig hCbig β hβ n₁ n₂ m q Omega X hq hqlog
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let gramScale : ℝ :=
    max (sampledRowGramSchatten Omega p X (q : ℝ))
      (sampledColumnGramSchatten Omega p X (q : ℝ))
  let varianceScale : ℝ := rademacherSampledVarianceScale Omega p X
  have hp : 0 ≤ p := by
    dsimp [p]
    exact sample_ratio_nonneg
  have hqReal : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ (2 : ℕ)) hq)
  have hGramBound :
      gramScale ≤ Real.exp (1 / 2) * varianceScale := by
    dsimp [gramScale, varianceScale, p]
    exact hGram Omega ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
      (q : ℝ) β hp hβ hqReal hqlog
  have hCcoreExp_le_Cbig : Ccore * Real.exp (1 / 2) ≤ Cbig :=
    le_trans (le_max_right (1 : ℝ) (Ccore * Real.exp (1 / 2))) hCbig
  have hVariance_nonneg : 0 ≤ varianceScale :=
    rademacherSampledVarianceScale_nonneg_of_nonneg Omega p X hp
  have hGram_nonneg : 0 ≤ gramScale :=
    sampledGramMax_nonneg_of_nonneg Omega p X (q : ℝ) hp
  have hLeftBase_nonneg :
      0 ≤ Ccore * Real.sqrt (q : ℝ) * gramScale := by
    exact mul_nonneg (mul_nonneg (le_of_lt hCcore) (Real.sqrt_nonneg _)) hGram_nonneg
  have hBase :
      Ccore * Real.sqrt (q : ℝ) * gramScale ≤
        Cbig * Real.sqrt (q : ℝ) * varianceScale := by
    calc
      Ccore * Real.sqrt (q : ℝ) * gramScale
          ≤ Ccore * Real.sqrt (q : ℝ) *
              (Real.exp (1 / 2) * varianceScale) := by
            exact mul_le_mul_of_nonneg_left hGramBound
              (mul_nonneg (le_of_lt hCcore) (Real.sqrt_nonneg _))
      _ = (Ccore * Real.exp (1 / 2)) *
            (Real.sqrt (q : ℝ) * varianceScale) := by ring
      _ ≤ Cbig * (Real.sqrt (q : ℝ) * varianceScale) := by
            exact mul_le_mul_of_nonneg_right hCcoreExp_le_Cbig
              (mul_nonneg (Real.sqrt_nonneg _) hVariance_nonneg)
      _ = Cbig * Real.sqrt (q : ℝ) * varianceScale := by ring
  have hPow :
      (Ccore * Real.sqrt (q : ℝ) * gramScale) ^ q ≤
        (Cbig * Real.sqrt (q : ℝ) * varianceScale) ^ q :=
    pow_le_pow_left₀ hLeftBase_nonneg hBase q
  exact le_trans
    (hCore β hβ n₁ n₂ m q Omega X hq hqlog)
    (by simpa [p, gramScale, varianceScale] using hPow)
