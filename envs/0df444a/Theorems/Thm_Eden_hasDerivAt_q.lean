-- Prove2me | Theorems.Thm_Eden_hasDerivAt_q
-- name    : Eden.hasDerivAt_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:18:57.981801+00:00
-- url     : https://prove2.me/theorems/b50f67d9-3f40-4587-ab86-12b1e2be85a3
-- title:
--   Eden: has Deriv At q
-- statement:
--   The Eden construction uses the has Deriv At q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VectorFieldDerivative.lean#L15-L20
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VectorFieldDerivative.lean#L15-L20

import Definitions.Def_Eden_CartesianDerivative
import Mathlib.LinearAlgebra.Trace
import Definitions.Def_Eden_VectorFieldDerivative
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.hasDerivAt_q (s : ℝ) : HasDerivAt q (-2 * s + 3) s := by sorry
