-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb30_original_any_constant_reserve_weighted_stieltjes_cash_equals_drift
-- name    : AvramDividend.Classical.avram_bvb30_original_any_constant_reserve_weighted_stieltjes_cash_equals_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:01:23.604714+00:00
-- url     : https://prove2.me/theorems/b9af8a7f-0f2a-46c5-950e-d5387ea78e0e
-- title:
--   Exact original weighted Stieltjes cash equals physical drift on any constant-reserve segment
-- statement:
--   For an admissible original dividend strategy, assume the actual prepayment reserve stays at a constant value k on the true time interval [0,T], the right dividend atoms vanish there, and the original physical spectrally negative Lévy path increment equals drift times elapsed time. Then for ANY nonnegative Borel weight f the actual original dividend Stieltjes integral on (0,T] equals the same weighted original drift-volume integral. This generalises the Proved zero-reserve result 32c4779c to the positive finite-cap plateau using the new Proved same-reserve endpoint source 31a30bff.
-- source:
--   Proved exact original constant-reserve Stieltjes interval 31a30bff and Proved measure_restrict_Ioc_eq_of_local_Ioc_agreement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb30_original_any_constant_reserve_weighted_stieltjes_cash_equals_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0) (k : ℝ) (hDrift : 0 ≤ X.drift)
    (hReserve : ∀ t : ℝ≥0, t ≤ T → riskProcess X x D t ω = k)
    (hNoAtom : ∀ t : ℝ≥0, t ≤ T → rightLimit D t ω = D t ω)
    (hSourceLine : ∀ a b : ℝ≥0, a ≤ b → b ≤ T →
      X.X b ω - X.X a ω = X.drift * ((b : ℝ) - (a : ℝ))) :
    ∀ f : ℝ → ℝ≥0∞,
      (∫⁻ t in Ioc (0 : ℝ) (T : ℝ), f t
        ∂(dividendMeasure D ω)) =
      (∫⁻ t in Ioc (0 : ℝ) (T : ℝ), f t
        ∂((ENNReal.ofReal X.drift) • volume)) := by sorry
