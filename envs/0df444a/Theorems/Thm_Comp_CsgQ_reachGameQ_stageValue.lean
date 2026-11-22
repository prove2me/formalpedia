-- Prove2me | Theorems.Thm_Comp_CsgQ_reachGameQ_stageValue
-- name    : Comp.CsgQ.reachGameQ_stageValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:54:00.610984+00:00
-- url     : https://prove2.me/theorems/77590578-7511-4c42-8ef8-61cb71dfd86d
-- title:
--   Csg Q: reach Game Q stage Value
-- statement:
--   Hence the two have the same value. Entrywise equality into
--       `MatrixGame.abs_value_sub_le` at `ε = 0`, exactly as in `Comp/Shapley.lean` and for the same
--       reason: `MatrixGame` has no `@[ext]` lemma, so an already-proved Lipschitz bound is the robust
--       way to get an equality.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L150-L162
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L150-L162

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Reach
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.reachGameQ_stageValue (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) (s : S) (v : S → ℚ)
    (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) :
    (G.toCSG h).stageValue s (fun s' => ((castIcc v h0 h1 s' : ℝ)))
      = (G.reachGameQ s v).toMatrixGame.value := by sorry
