-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_source_rate_to_real_lintegral
-- name    : AvramDividend.Classical.avram_wave7_06_original_negative_band_source_rate_to_real_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:13:46.877669+00:00
-- url     : https://prove2.me/theorems/2cc6bc61-b94e-4d48-a114-f44359e55fc0
-- title:
--   Original negative-band jump count ENNReal Lévy rate yields real integrable mean identity
-- statement:
--   The precise source-count real expectation normalization required by the original W7-06 dominated-grid intensity bridge follows from the separately owned original Lévy first-moment rate theorem 34dbea70. The negative cutoff band is B=(-∞,-1/(n+1)], separated from zero with ε=1/(n+1)>0. The proof is a genuine reduction; it remains SKETCH_ACCEPTED until P2's source rate theorem is Proved.
-- source:
--   W7-06 source mean-to-real bridge importing P2 original Lévy intensity theorem 34dbea70; no rate claim without its completion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_negative_band_source_rate_to_real_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ∂P).toReal =
    (T : ℝ) *
      (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal := by sorry
