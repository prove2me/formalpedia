-- Prove2me | Theorems.Thm_Eden_planarDiagonal_comp_self
-- name    : Eden.planarDiagonal_comp_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:30:37.636055+00:00
-- url     : https://prove2.me/theorems/247c6edf-2e43-495e-999a-70d16d3d5ba8
-- title:
--   Eden: planar Diagonal comp self
-- statement:
--   The Eden construction uses the planar Diagonal comp self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarSingularValues.lean#L29-L33
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarSingularValues.lean#L29-L33

import Definitions.Def_Eden_PlanarDerivative
import Definitions.Def_Eden_StationaryFactors
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_PlanarSingularValues
set_option autoImplicit true
noncomputable section
open Polynomial
open Eden

theorem Eden.planarDiagonal_comp_self (d : PlanarSpace) :
    planarDiagonal d ∘ₗ planarDiagonal d =
      planarDiagonal (WithLp.toLp 2 (fun i => d i ^ 2)) := by sorry
