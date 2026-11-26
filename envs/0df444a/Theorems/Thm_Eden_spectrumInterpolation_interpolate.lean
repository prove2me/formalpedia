-- Prove2me | Theorems.Thm_Eden_spectrumInterpolation_interpolate
-- name    : Eden.spectrumInterpolation_interpolate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:53:51.453941+00:00
-- url     : https://prove2.me/theorems/967fb122-27ae-5932-b18d-a31555f5d0f7
-- title:
--   Eden: spectrum Interpolation interpolate
-- statement:
--   The Eden construction uses the spectrum Interpolation interpolate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicInterpolation.lean#L46-L62
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicInterpolation.lean#L46-L62

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SingularValueFunction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Definitions.Def_Eden_LogarithmicInterpolation
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.spectrumInterpolation_interpolate (a : Fin 5 → ℝ) {k : ℕ} (hk : k < 5)
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    spectrumInterpolation a ((k : ℝ) + α) =
      spectrumPartialSum a k + α * spectrumEntry a k := by sorry
