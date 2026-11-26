-- Prove2me | Theorems.Thm_Eden_spectrumInterpolation_eq_range
-- name    : Eden.spectrumInterpolation_eq_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:48:55.552345+00:00
-- url     : https://prove2.me/theorems/b1bb305e-2bd8-4a97-bfac-3466266816ad
-- title:
--   Eden: spectrum Interpolation eq range
-- statement:
--   The Eden construction uses the spectrum Interpolation eq range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicInterpolation.lean#L36-L44
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicInterpolation.lean#L36-L44

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SingularValueFunction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Definitions.Def_Eden_LogarithmicInterpolation
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.spectrumInterpolation_eq_range (a : Fin 5 → ℝ) (d : ℝ) :
    spectrumInterpolation a d =
      ∑ i ∈ Finset.range 5, singularWeight i d * spectrumEntry a i := by sorry
