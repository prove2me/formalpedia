-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_original_canonical_openinterior_ruinclipped_grid_HJB_rightcash_sign
-- name    : AvramDividend.Classical.avram_jump6_original_canonical_openinterior_ruinclipped_grid_HJB_rightcash_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T20:57:33.959821+00:00
-- url     : https://prove2.me/theorems/82b1ff60-b40b-4375-8561-75b8ec88ff30
-- title:
--   Exact canonical ruin-clipped physical open-interior HJB grid plus strict preruin right-dividend correction is nonpositive
-- statement:
--   For every original spectrally negative Lévy process and true clipped physical grid v_i=min(i*n/(m+1),σ(ω)), choose active_i to be precisely the decidable original pre-payment reserve's open HJB interior condition (strict positivity and below the original cap). Derive automatically that each selected cell satisfies generator nonpositivity, and that every clipped physical grid interval is ordered using multiplication monotonicity and min. With the genuine original right-dividend jump-value-drop HJB condition and the actual finite pre-ruin payment-mark set, prove the complete discounted physical generator residual and right-payment correction is nonpositive. This removes auxiliary active/mesh hypotheses of Proved b239 and supplies the canonical signed source term for original stopped Itô–Meyer finite-grid verification.
-- source:
--   Proved b239 original HJB/rightdividend signed source 316fb152-4993-4218-b6a2-b24fe4d6499c. The originally open full Ito physical source 15815eff and current initial-event full-grid source target 7a944609 need canonical open interior grid conditions without arbitrary external assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b239_original_ruinclipped_physical_generator_and_right_payment_cash_negative
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_jump6_original_canonical_openinterior_ruinclipped_grid_HJB_rightcash_sign
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ η (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D η) →
      rightLimit D t η - D t η ≤
        w (riskProcess X x D t η) -
          w (riskProcess X x D t η -
            (rightLimit D t η - D t η)))
    (σ : Ω → ℝ≥0) (n m : ℕ) (ω : Ω)
    (R : Finset ℝ≥0)
    (hPre : ∀ u ∈ R,
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
    let active : ℕ → Bool := fun i =>
      decide (0 < riskProcess X x D (v i) ω ∧
        ENNReal.ofReal (riskProcess X x D (v i) ω) < C)
    (∑ i ∈ Finset.range m, if active i then
      Real.exp (-(q * (v i : ℝ))) *
        ((v (i + 1) : ℝ) - (v i : ℝ)) *
        (X.generator w (riskProcess X x D (v i) ω) -
          q * w (riskProcess X x D (v i) ω))
      else 0) +
    (∑ u ∈ R, Real.exp (-(q * (u : ℝ))) *
      ((rightLimit D u ω - D u ω) -
        (w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω))))) ≤ 0 := by sorry
