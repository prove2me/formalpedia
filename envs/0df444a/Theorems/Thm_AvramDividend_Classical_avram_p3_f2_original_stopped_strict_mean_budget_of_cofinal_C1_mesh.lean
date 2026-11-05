-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_strict_mean_budget_of_cofinal_C1_mesh
-- name    : AvramDividend.Classical.avram_p3_f2_original_stopped_strict_mean_budget_of_cofinal_C1_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:36:45.877639+00:00
-- url     : https://prove2.me/theorems/28343e2d-7a82-4210-846d-a6af569b97be
-- title:
--   Actual original stopped strict C1 mesh expected budgets pass to the full payoff
-- statement:
--   This is a source-exact original controlled Lévy/Stieltjes and fixed strict-survival terminal bridge. It derives all cash and terminal integrability from proved admissibility/BV lemmas and passes any uniform finite-cofinal-mesh expected source budget to the true original stopped strict-horizon expected payoff. The only additional hypothesis is the actual source mesh expected inequality that P3-F2 must obtain from its finite C1 chain, jump compensation and HJB signs; horizon atoms remain P3-G2's concern.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_expected_tendsto_real
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_stopped_strict_mean_budget_of_cofinal_C1_mesh
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hu : ∀ n, 0 ≤ u n) (hbelow : ∀ n, u n ≤ (S : ℝ))
    (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n)
    (K : ℝ)
    (hMesh : ∀ n,
      (∫ ω : Ω,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
        else 0) ∂P) ≤ K) :
    (∫ ω : Ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ K := by sorry
