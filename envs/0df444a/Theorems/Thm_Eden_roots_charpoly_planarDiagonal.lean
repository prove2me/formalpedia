-- Prove2me | Theorems.Thm_Eden_roots_charpoly_planarDiagonal
-- name    : Eden.roots_charpoly_planarDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:59.966499+00:00
-- url     : https://prove2.me/theorems/a8bc40ec-d82e-53d7-9b97-78484e5caadd
-- title:
--   Eden: roots charpoly planar Diagonal
-- statement:
--   The Eden construction uses the roots charpoly planar Diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarSingularValues.lean#L42-L47
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarSingularValues.lean#L42-L47

import Definitions.Def_Eden_PlanarDerivative
import Definitions.Def_Eden_StationaryFactors
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_PlanarSingularValues
set_option autoImplicit true
noncomputable section
open Polynomial
open Eden

theorem Eden.roots_charpoly_planarDiagonal (d : PlanarSpace) :
    (planarDiagonal d).charpoly.roots = Finset.univ.val.map (fun i => d i) := by sorry
