-- Prove2me | Theorems.Thm_Eden_diagonalLinear_bijective
-- name    : Eden.diagonalLinear_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:18:01.706187+00:00
-- url     : https://prove2.me/theorems/57a26ba7-80f3-4927-a2cb-37f6f79430c1
-- title:
--   Eden: diagonal Linear bijective
-- statement:
--   The Eden construction uses the diagonal Linear bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DerivativeDecomposition.lean#L87-L98
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DerivativeDecomposition.lean#L87-L98

import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_DerivativeDecomposition
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.diagonalLinear_bijective {d : PhaseSpace} (hd : ∀ i, d i ≠ 0) :
    Function.Bijective (diagonalLinear d) := by sorry
