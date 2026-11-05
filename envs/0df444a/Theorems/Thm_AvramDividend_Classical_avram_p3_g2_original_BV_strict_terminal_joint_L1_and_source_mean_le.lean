-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_strict_terminal_joint_L1_and_source_mean_le
-- name    : AvramDividend.Classical.avram_p3_g2_original_BV_strict_terminal_joint_L1_and_source_mean_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:34:12.448762+00:00
-- url     : https://prove2.me/theorems/e88885b6-b55a-43ab-94b9-07cabd2544a5
-- title:
--   Original bounded-variation stopped terminal joint L1 and expected postpayment domination from genuine Lévy fields
-- statement:
--   At every deterministic original ruin-truncated clock, simultaneously establish strict-survival post-rightpayment terminal integrability, prepayment terminal integrability and the expected postpayment ≤ prepayment inequality. X.X_zero and X.isProbability discharge the only extra technical premises, and the result uses the actual original admissible D and any positive or infinite cap without a boundary-occupation shortcut. This is the complete terminal interface for P3's strict prebudget-to-signed-horizon transfer, leaving its stochastic prebudget independently open.
-- source:
--   Proved public 533559a4 source terminal L1, d50ca317 expected domination, original preterminal L1 d086b85a, and actual SpectrallyNegativeLevy record fields. Canonical residual 7bb152c2 and signed/prebudget Open; no imports from those targets.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_preterminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_BV_strict_survival_postpayment_terminal_L1_from_source
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_BV_strict_survival_postpayment_expected_le_preterminal

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_BV_strict_terminal_joint_L1_and_source_mean_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (S : ℝ≥0) :
    let Post : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0
    let Pre : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) *
          w (riskProcess X x D S ω)
      else 0
    Integrable Post P ∧ Integrable Pre P ∧
      (∫ ω, Post ω ∂P) ≤ (∫ ω, Pre ω ∂P) := by sorry
