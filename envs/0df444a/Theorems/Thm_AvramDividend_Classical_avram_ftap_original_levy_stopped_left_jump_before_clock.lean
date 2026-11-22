-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ftap_original_levy_stopped_left_jump_before_clock
-- name    : AvramDividend.Classical.avram_ftap_original_levy_stopped_left_jump_before_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:46:56.790366+00:00
-- url     : https://prove2.me/theorems/6c9aa3bd-7317-4efc-9cf8-340ac463de80
-- title:
--   Original stopped Lévy path retains the full physical left jump at and before the stopping clock
-- statement:
--   At every original physical time t no later than an arbitrary stopping clock τ, the stopped Lévy driver has precisely the same left jump X_t-X_{t-} as the unstopped driver. The full stopped jump at τ is included. Adapts FTAPTheorem42/Foundations/Paths.lean proof processLeftJump_stoppedProcess_eq_of_le (commit 8c9c46e1b6e455f7d3069062957d4363879836ce, Apache-2.0) to Avram's actual SpectrallyNegativeLevy.X field and its already-defined all-path X.leftLim property. No fake or assumed jump reward.
-- source:
--   https://github.com/selpoG/lean-ftap-closedness/blob/8c9c46e1b6e455f7d3069062957d4363879836ce/FTAPTheorem42/Foundations/Paths.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Filter MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_ftap_original_levy_stopped_left_jump_before_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) (t : ℝ≥0)
    (ht : (t : WithTop ℝ≥0) ≤ τ ω) :
    MeasureTheory.stoppedProcess X.X τ t ω -
      Function.leftLim
        (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X τ s ω) t =
    X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t := by sorry
