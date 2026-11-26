-- Prove2me | Theorems.Thm_Eden_planarDiagonal_apply
-- name    : Eden.planarDiagonal_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:22:43.653678+00:00
-- url     : https://prove2.me/theorems/23b073b0-f468-43e5-bde7-1ad24d491f1f
-- title:
--   Eden: planar Diagonal apply
-- statement:
--   The Eden construction uses the planar Diagonal apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarDerivative.lean#L118-L119
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarDerivative.lean#L118-L119

import Definitions.Def_Eden_PlanarVectorField
import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_PlanarDerivative
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.planarDiagonal_apply (d v : PlanarSpace) (i : Fin 2) :
    planarDiagonal d v i = d i * v i := by sorry

attribute [defeq] Eden.planarDiagonal_apply
