-- Prove2me | Theorems.Thm_Eden_diagonalLinear_apply
-- name    : Eden.diagonalLinear_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:17:31.823436+00:00
-- url     : https://prove2.me/theorems/cea19c28-1c78-4ffe-bf59-d2eb1e6b1c7b
-- title:
--   Eden: diagonal Linear apply
-- statement:
--   The Eden construction uses the diagonal Linear apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DerivativeDecomposition.lean#L21-L22
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DerivativeDecomposition.lean#L21-L22

import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_DerivativeDecomposition
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.diagonalLinear_apply (d v : PhaseSpace) (i : Fin 5) :
    diagonalLinear d v i = d i * v i := by sorry

attribute [defeq] Eden.diagonalLinear_apply
