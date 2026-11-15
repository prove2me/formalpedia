-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb44_original_finitecap_C1_any_constant_reserve_fullT_compensated_cash
-- name    : AvramDividend.Classical.avram_bvb44_original_finitecap_C1_any_constant_reserve_fullT_compensated_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:35:27.898767+00:00
-- url     : https://prove2.me/theorems/acf78d26-851f-4f01-8683-1da8b2a25c2d
-- title:
--   Original Standing BV C1 finite-cap original Stieltjes full-T compensated cash on arbitrary constant reserve plateau
-- statement:
--   Under the FULL original Standing BV finiteactivity C1 HJB hypotheses, including 0≤w(0), continuous w on nonnegative reserve, C1 interior and derivative≥1, bound genuine original discounted D Stieltjes cash plus original true-T terminal exp(-qT)w(r) at EVERY constant controlled reserve level r∈[0,C], assuming physical X is drift-only on [0,T] and original D has no right atoms. Preserve true original negative-jump ν compensator, original cap, original time and controlled reserve. Sound exhaustive r=0 or r>0 reduction: use Proved stronger-original zero plateau source bvb43 and Proved weak-assumption positive plateau bvb41. This is the complete constant-reserve contact ledger source for the BV mission.
-- source:
--   Proved positive original finitecap plateau 265ab88e; original strong C1 zero plateau bvb43 a36e9144, plus original Stieltjes and HJB sources.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Filter Set intervalIntegral AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb44_original_finitecap_C1_any_constant_reserve_fullT_compensated_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ))) (hw0 : 0 ≤ w 0)
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
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
