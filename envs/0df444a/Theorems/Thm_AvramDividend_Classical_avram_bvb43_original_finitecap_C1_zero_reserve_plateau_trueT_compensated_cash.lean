-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb43_original_finitecap_C1_zero_reserve_plateau_trueT_compensated_cash
-- name    : AvramDividend.Classical.avram_bvb43_original_finitecap_C1_zero_reserve_plateau_trueT_compensated_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:33:53.381909+00:00
-- url     : https://prove2.me/theorems/a36e9144-8658-4ade-b5fc-1f360d7ee48b
-- title:
--   Original finitecap Standing BV C1 zero-reserve plateau actual dividend plus terminal compensated full-T cash budget
-- statement:
--   Source-faithful endpoint case under the actual original full BV mission assumptions including finite activity, C1 interior regularity and nonnegative w(0). The original admissible controlled reserve remains zero on [0,T], right dividend atoms vanish and physical X has no negative jumps so exact original drift. Then original discounted D Stieltjes dividends plus true-T discounted terminal w(0) are bounded by w(0) minus the TRUE original negative mark compensator times discounted interval integral. Direct consequence of Proved bvb28 zero-boundary discounted budget 2c12049b and Proved bvb30/bvb31 actual Stieltjes drift conversion. This closes the original zero-contact plateau branch with full source hypotheses; no weak-HJB conjecture.
-- source:
--   Proved 2c12049b original zero C1 HJB, b9af8a7f original weighted D plateau cash, 1346e9f7 discounted volume conversion, 0432f641 Standing BV positive drift.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Filter Set intervalIntegral AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb43_original_finitecap_C1_zero_reserve_plateau_trueT_compensated_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hwCont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (hReserveZero : ∀ t : ℝ≥0, t ≤ T →
      riskProcess X x D t ω = 0)
    (hNoAtom : ∀ t : ℝ≥0, t ≤ T →
      rightLimit D t ω = D t ω)
    (hSourceLine : ∀ a b : ℝ≥0, a ≤ b → b ≤ T →
      X.X b ω - X.X a ω =
        X.drift * ((b : ℝ) - (a : ℝ))) :
    (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp ((-q) * t))
        ∂(dividendMeasure D ω)).toReal +
      Real.exp ((-q) * (T : ℝ)) * w 0 ≤
    w 0 -
      (∫ z in Iio (0 : ℝ),
        w ((0 : ℝ) + z) - w 0 ∂X.ν) *
      (∫ t in (0 : ℝ)..(T : ℝ), Real.exp ((-q) * t)) := by sorry
