-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb37_original_finitecap_any_constant_reserve_discounted_cash_budget
-- name    : AvramDividend.Classical.avram_bvb37_original_finitecap_any_constant_reserve_discounted_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:18:55.576714+00:00
-- url     : https://prove2.me/theorems/0bbacd5f-e314-41be-9322-fe174adcfa96
-- title:
--   Original finitecap all-reserve constant-level actual discounted dividend plus terminal compensator budget
-- statement:
--   For the actual original finiteactivity Standing BV spectrally negative Levy process and original admissible dividend D, with the controlled reserve fixed at ANY real r∈[0,C] throughout [0,T], no right D atoms, and exact original driver drift-linearity on the same interval, bound discounted actual original Stieltjes dividend cash plus true-T exp(-qT)w(r) by w(r) minus the genuinely compensated negative-mark kernel at r times discounted time. Use Proved physical closed-band generator source aa00b80d, positive original drift, HJB slope at interior, and Proved b9af8a7f and 1346e9f7 exact original measure conversion. No replacement driver, reserve, stopping, terminal or ν.
-- source:
--   Proved aa00b80d original closed-band BV HJB, Proved b9af8a7f original Stieltjes plateau, Proved 1346e9f7 weighted drift-volume conversion, Proved 5ce1f298 exact discounted integral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Filter Set intervalIntegral AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb37_original_finitecap_any_constant_reserve_discounted_cash_budget
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
