-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb41_original_finitecap_zero_constant_reserve_discounted_cash_budget
-- name    : AvramDividend.Classical.avram_bvb41_original_finitecap_zero_constant_reserve_discounted_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:28:03.694973+00:00
-- url     : https://prove2.me/theorems/a773dc60-782b-4d5c-8de0-424ed2f1d0ec
-- title:
--   Original BV finite-cap zero controlled reserve plateau full horizon compensated discounted cash bound
-- statement:
--   Strengthening of the original all-band constant reserve level source 0bbacd5f with the additional (hrZero : r = 0) hypothesis. Prove actual original D discounted Stieltjes cash plus genuine full-T discounted w(r) bounded by initial w(r) minus original negative mark kernel times discounted clock. Positive case follows Proved 32ce498d closed cap and c8ba98f0 interior generator identity with slope≥1. Zero case requires deriving original zero-boundary HJB without additional hw0 or ContDiffOn premises. The two cases partition all r≥0 and retain original ν, clock, D.
-- source:
--   Original same-band source 0bbacd5f; Proved 1346e9f7, b9af8a7f, 32ce498d, c8ba98f0, plus undisputed original boundary HJB source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Filter Set intervalIntegral AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb41_original_finitecap_zero_constant_reserve_discounted_cash_budget
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
    (ω : Ω) (T : ℝ≥0) (r : ℝ)
    (hr0 : 0 ≤ r) (hrC : r ≤ C.toReal)
    (hrZero : r = 0)
    (hReserve : ∀ t : ℝ≥0, t ≤ T →
      riskProcess X x D t ω = r)
    (hNoAtom : ∀ t : ℝ≥0, t ≤ T → rightLimit D t ω = D t ω)
    (hSourceLine : ∀ a b : ℝ≥0, a ≤ b → b ≤ T →
      X.X b ω - X.X a ω =
        X.drift * ((b : ℝ) - (a : ℝ))) :
    (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp ((-q) * t))
        ∂(dividendMeasure D ω)).toReal +
      Real.exp ((-q) * (T : ℝ)) * w r ≤
    w r -
      (∫ z in Iio (0 : ℝ),
        w (r + z) - w r ∂X.ν) *
      (∫ t in (0 : ℝ)..(T : ℝ), Real.exp ((-q) * t)) := by sorry
