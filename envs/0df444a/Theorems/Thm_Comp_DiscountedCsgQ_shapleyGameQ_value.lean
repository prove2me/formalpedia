-- Prove2me | Theorems.Thm_Comp_DiscountedCsgQ_shapleyGameQ_value
-- name    : Comp.DiscountedCsgQ.shapleyGameQ_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:54:36.688815+00:00
-- url     : https://prove2.me/theorems/727f09d5-b0d4-4641-b0b0-13bf656fbf26
-- title:
--   Discounted Csg Q: shapley Game Q value
-- statement:
--   The two stage games have the same value. Entrywise equality fed to
--       `MatrixGame.abs_value_sub_le` at `ε = 0`, as the module docstring explains -- no `MatrixGame`
--       equality and no `ext`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Shapley.lean#L81-L90
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Shapley.lean#L81-L90

import Definitions.Def_Comp_Search
import Definitions.Def_Comp_Shapley
set_option autoImplicit true
open Comp
open Csg
open Comp.DiscountedCsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

theorem Comp.DiscountedCsgQ.shapleyGameQ_value (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed) (s : S) (v : S → ℚ) :
    ((G.toDiscountedCSG h).shapleyGame s (fun s' => ((v s' : ℚ) : ℝ))).value
      = (G.shapleyGameQ s v).toMatrixGame.value := by sorry
