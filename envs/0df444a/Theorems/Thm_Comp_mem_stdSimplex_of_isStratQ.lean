-- Prove2me | Theorems.Thm_Comp_mem_stdSimplex_of_isStratQ
-- name    : Comp.mem_stdSimplex_of_isStratQ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:09:32.689834+00:00
-- url     : https://prove2.me/theorems/1b1ae72d-bd3a-43c9-a177-3f545e3664fa
-- title:
--   Comp: mem std Simplex of is Strat Q
-- statement:
--   A rational mixed strategy casts to a point of the real standard simplex. The bridge every
--       statement below uses to hand a rational witness to a theorem stated over `ℝ`.
--
--       Both branches open with `change` to force the beta-reduced form: membership in `stdSimplex ℝ I`
--       unfolds with the witness still applied as `(fun i => ↑(p i)) i`, and `norm_cast` does not see
--       through an unreduced application, so `exact_mod_cast` fails against it. Beta is definitional,
--       so `change` is free.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/MatrixGameQ.lean#L86-L94
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/MatrixGameQ.lean#L86-L94

import Definitions.Def_Comp_Basic
import Definitions.Def_Comp_MatrixGameQ
set_option autoImplicit true
open Comp
open Csg
variable {I : Type*} [Fintype I]

theorem Comp.mem_stdSimplex_of_isStratQ {p : I → ℚ} (h : IsStratQ p) :
    (fun i => ((p i : ℚ) : ℝ)) ∈ stdSimplex ℝ I := by sorry
