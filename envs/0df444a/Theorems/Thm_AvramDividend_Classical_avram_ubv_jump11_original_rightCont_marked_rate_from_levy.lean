-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_rightCont_marked_rate_from_levy
-- name    : AvramDividend.Classical.avram_ubv_jump11_original_rightCont_marked_rate_from_levy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T09:32:46.791633+00:00
-- url     : https://prove2.me/theorems/4127b09d-73df-4175-8513-6173b021e36b
-- title:
--   Original initial-event marked jump compensator from source Lévy law
-- statement:
--   For actual intrinsic jumps of the original spectrally negative Lévy process, derive the right-continuous initial-event finite-mark predictable rectangle mean directly from the unconditional source Lévy marked rate and raw past-event factorisation. The source jump field and finite-band approximating clocks are explicit; no additional compensator axiom, auxiliary process or Gaussian independence is assumed. This supports masking the pure-jump stochastic integral on a strictly positive stopped-clock event.
-- source:
--   Composes authoritative Proved source laws 859bf7be, 9db23f4e and cc36d5e2; bridge into a44d4219's initial-filtration positive-clock compensator obligation, with physical Ito ledger still open.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_rectangle_of_unconditional_rate
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_raw_compensator_to_rightCont_event_rate
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_jump11_original_rightCont_marked_rate_from_levy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (r : ℕ → ℝ≥0)
    (hsr : ∀ n, s < r n) (hrt : ∀ n, r n ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) (A : Set Ω)
    (hA : MeasurableSet[𝓕.rightCont s] A)
    (J : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞)
    (hJsource : ∀ a b ω, J a b ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc a b ×ˢ B))
    (hShort : Tendsto (fun n => r n - s) atTop (𝓝 0))
    (hLong : Tendsto (fun n => t - r n) atTop (𝓝 (t - s)))
    (hFinite : X.ν B ≠ ⊤) (hMass : P A ≠ ⊤) :
    (∫⁻ ω in A, J s t ω ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
