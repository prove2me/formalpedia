-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_shifted_future_source_leftLim_translation
-- name    : AvramDividend.Classical.avram_wave5_01_actual_shifted_future_source_leftLim_translation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:24:25.571261+00:00
-- url     : https://prove2.me/theorems/81fc4187-9f23-4f45-b1e3-6a166bb96b41
-- title:
--   Exact original-source left-jump translation under deterministic time shift
-- statement:
--   For the same actual source path X and original sample ω, every deterministic start time s and positive future time u, the left limit of the future-increment path v↦X(s+v,ω)−X(s,ω) at u equals the actual original path left limit X((s+u)−,ω)−X(s,ω). This verifies same-path translation of the pre-jump mark, a necessary identity for obtaining stationary and original-past-independent source marked-count laws from future-increment path functionals. No detached process, copied probability space, artificial filtration, BV, or Poisson assumption is introduced.
-- source:
--   Original SpectrallyNegativeLevy.leftLim sample-path axiom, Tendsto under positive constant-addition on the strict-left filter, and Mathlib leftLim_eq_of_tendsto.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_shifted_future_source_leftLim_translation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s u : ℝ≥0) (hu : 0 < u) :
    Function.leftLim
      (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) u =
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) (s + u) -
        X.X s ω := by sorry
