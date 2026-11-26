-- Prove2me | Theorems.Thm_Eden_globalLyapunovDimension_eq_supremum_asymptoticDimension
-- name    : Eden.globalLyapunovDimension_eq_supremum_asymptoticDimension
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:04:06.347033+00:00
-- url     : https://prove2.me/theorems/009e34df-765e-4613-bc09-625d8a92d37c
-- title:
--   Eden: global Lyapunov Dimension eq supremum asymptotic Dimension
-- statement:
--   The Eden construction uses the global Lyapunov Dimension eq supremum asymptotic Dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L149-L152
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L149-L152

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.globalLyapunovDimension_eq_supremum_asymptoticDimension {c : ℝ} (hc : 4 < c) :
    globalLyapunovDimension c attractor = sSup (asymptoticDimension c '' attractor) := by sorry
