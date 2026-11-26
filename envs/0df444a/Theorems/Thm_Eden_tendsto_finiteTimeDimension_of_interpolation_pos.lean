-- Prove2me | Theorems.Thm_Eden_tendsto_finiteTimeDimension_of_interpolation_pos
-- name    : Eden.tendsto_finiteTimeDimension_of_interpolation_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:57:45.032914+00:00
-- url     : https://prove2.me/theorems/6d55d6f0-06d1-41eb-aa56-066dada4a8d0
-- title:
--   Eden: tendsto finite Time Dimension of interpolation pos
-- statement:
--   The Eden construction uses the tendsto finite Time Dimension of interpolation pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionConvergenceCriteria.lean#L61-L74
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionConvergenceCriteria.lean#L61-L74

import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_DimensionConvergenceCriteria
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.tendsto_finiteTimeDimension_of_interpolation_pos (c : ℝ) (p : PhaseSpace)
    (hpos : ∀ d ∈ Ioo 0 (asymptoticDimension c p),
      0 < spectrumInterpolation (lyapunovExponent c p) d) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by sorry
