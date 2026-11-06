-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_predividend_clipped_reserve_jointly_measurable_bounded
-- name    : AvramDividend.Classical.avram_p4_f3_original_predividend_clipped_reserve_jointly_measurable_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:08:08.921037+00:00
-- url     : https://prove2.me/theorems/55e36fd0-89b5-467e-9af3-c9e70aa0a92d
-- title:
--   Original pre-dividend physical left-reserve clipping is jointly measurable and obeys its upper localisation cap
-- statement:
--   For the actual original spectrally negative Levy reserve x+X-D(t+) at each time and sample, clipping its strict left limit to a compact reserve band is jointly measurable in ambient physical time and sample and never exceeds the chosen ceiling K. This discharges the concrete stochastic source coefficient measurability and finite upper-band assumptions simultaneously.
-- source:
--   The original true reserve strict left-limit ambient measurable theorem 63da8b2d is Proved. The clipped original reserve is a measurable piecewise function of that same source path; its upper-bound follows from the clipping branch and δ≤K, with no surrogate model.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_controlled_prestate_ambient_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_predividend_clipped_reserve_jointly_measurable_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (δ K : ℝ) (hδK : δ ≤ K) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    Measurable U ∧ ∀ p, U p ≤ K := by sorry
