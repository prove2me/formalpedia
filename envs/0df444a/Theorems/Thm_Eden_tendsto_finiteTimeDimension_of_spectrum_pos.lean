-- Prove2me | Theorems.Thm_Eden_tendsto_finiteTimeDimension_of_spectrum_pos
-- name    : Eden.tendsto_finiteTimeDimension_of_spectrum_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:21.102889+00:00
-- url     : https://prove2.me/theorems/8d372c43-e618-48d5-9c32-d4149544bae6
-- title:
--   Eden: tendsto finite Time Dimension of spectrum pos
-- statement:
--   The Eden construction uses the tendsto finite Time Dimension of spectrum pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionConvergence.lean#L27-L34
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionConvergence.lean#L27-L34

import Definitions.Def_Eden_DimensionConvergenceCriteria
import Definitions.Def_Eden_NeutralDimensionBounds
import Definitions.Def_Eden_LimitingInterpolation
import Definitions.Def_Eden_DimensionConvergence
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.tendsto_finiteTimeDimension_of_spectrum_pos (c : ℝ) (p : PhaseSpace)
    (a : Fin 5 → ℝ) (ha : lyapunovExponent c p = a)
    (hpos : ∀ d ∈ Ioo 0 (kaplanYorkeDimension a), 0 < spectrumInterpolation a d) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by sorry
