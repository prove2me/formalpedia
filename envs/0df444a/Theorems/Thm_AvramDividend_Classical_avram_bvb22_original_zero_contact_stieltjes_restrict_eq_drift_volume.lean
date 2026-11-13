-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_contact_stieltjes_restrict_eq_drift_volume
-- name    : AvramDividend.Classical.avram_bvb22_original_zero_contact_stieltjes_restrict_eq_drift_volume
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:12:21.14422+00:00
-- url     : https://prove2.me/theorems/4ae551cd-7136-4580-a1a9-3d4c9b208889
-- title:
--   Original finite-activity zero-contact Stieltjes cash measure equals physical drift times volume throughout an active source-linear horizon
-- statement:
--   If the original admissible BV dividend strategy remains at zero controlled reserves throughout a positive activity horizon and the underlying process follows its physical drift with no jumps, then its restricted Stieltjes dividend measure equals physical drift times Lebesgue measure, on the same horizon. This identity retains the exact zero-contact dividend cash and may be used to derive its discounted compensator bound instead of discarding zero reserve by an open-grid mask. The local source contact-mass and finite-window measure uniqueness theorems are both Proved imports.
-- source:
--   Proved original source zero-contact Stieltjes Ioc cash equality 28a916cf and measure restriction uniqueness 7ba7a474; Avram-Palmowski-Pistorius Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_active_zero_contact_Ioc_cash_eq_drift
import Theorems.Thm_AvramDividend_Classical_measure_restrict_Ioc_eq_of_local_Ioc_agreement
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb22_original_zero_contact_stieltjes_restrict_eq_drift_volume
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ) (hT : 0 ≤ T) (hd : 0 ≤ X.drift)
    (hCashFinite : dividendMeasure D ω (Ioc (0 : ℝ) T) < ⊤)
    (hZero : ∀ t : ℝ≥0, (t : ℝ) ≤ T → riskProcess X x D t ω = 0)
    (hActive : ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (hLine : ∀ a b : ℝ≥0, a ≤ b → (b : ℝ) ≤ T →
      X.X b ω - X.X a ω = X.drift * ((b : ℝ) - (a : ℝ))) :
    (dividendMeasure D ω).restrict (Ioc 0 T) =
      (ENNReal.ofReal X.drift • (volume : Measure ℝ)).restrict (Ioc 0 T) := by sorry
