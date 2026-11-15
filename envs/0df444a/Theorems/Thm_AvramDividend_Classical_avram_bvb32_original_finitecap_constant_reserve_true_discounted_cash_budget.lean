-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb32_original_finitecap_constant_reserve_true_discounted_cash_budget
-- name    : AvramDividend.Classical.avram_bvb32_original_finitecap_constant_reserve_true_discounted_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:06:59.165079+00:00
-- url     : https://prove2.me/theorems/173e4faf-1e57-4e3a-902a-6dc2e4f06936
-- title:
--   Original finite-cap constant-cap-reserve discounted cash and true horizon compensator budget
-- statement:
--   Assume the ACTUAL original Standing bounded-variation spectrally negative Lévy process has finite jump activity, finite positive cap C, original smooth HJB supersolution w, actual admissible left-continuous dividend D, original reserve is exactly C throughout [0,T], no D right endpoint atoms on this interval, and original driver has no negative marks and hence is drift-linear on [0,T]. Then the original discounted dividend measure integral plus genuine terminal discounted w(C) is bounded by initial w(C) minus the ORIGINAL compensated negative-mark integral times discounted time. This is the exact cap-plateau true T Stieltjes case and does not replace ν or the original process. Combine Proved b9af8a7f and f2242dea with bvb31.
-- source:
--   Proved 31a30bff, b9af8a7f, f2242dea, 0432f641; new bvb31 correct real drift-volume conversion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Filter Set intervalIntegral AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb32_original_finitecap_constant_reserve_true_discounted_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (hReserve : ∀ t : ℝ≥0, t ≤ T →
      riskProcess X x D t ω = C.toReal)
    (hNoAtom : ∀ t : ℝ≥0, t ≤ T → rightLimit D t ω = D t ω)
    (hSourceLine : ∀ a b : ℝ≥0, a ≤ b → b ≤ T →
      X.X b ω - X.X a ω =
        X.drift * ((b : ℝ) - (a : ℝ))) :
    (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp ((-q) * t))
        ∂(dividendMeasure D ω)).toReal +
      Real.exp ((-q) * (T : ℝ)) * w C.toReal ≤
    w C.toReal -
      (∫ z in Iio (0 : ℝ),
        w (C.toReal + z) - w C.toReal ∂X.ν) *
      (∫ t in (0 : ℝ)..(T : ℝ), Real.exp ((-q) * t)) := by sorry
