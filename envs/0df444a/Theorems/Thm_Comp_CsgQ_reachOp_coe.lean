-- Prove2me | Theorems.Thm_Comp_CsgQ_reachOp_coe
-- name    : Comp.CsgQ.reachOp_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:52:39.267686+00:00
-- url     : https://prove2.me/theorems/78b8e3c6-9f48-46b4-9b94-7152c0cde03e
-- title:
--   Csg Q: reach Op coe
-- statement:
--   `reachOp`'s coercion as a subtype-free, `ℝ`-valued `if`-`then`-`else`. Without this, `change`
--       cannot reach past the `Set.Icc` packaging: the `ite` sits on an abstract `DecidablePred goal`
--       instance and so will not reduce definitionally, whatever the ambient hypothesis says about
--       `goal s`. The fix is `Csg/CoBuchiOp.lean`'s own `coBuchiInnerOpFun_coe`, verbatim --
--       `unfold`, then `split_ifs <;> rfl` -- and with it in hand `if_pos`/`if_neg` work as
--       ordinary rewrite lemmas, which is how `Csg/CoalitionComplementReach.lean` handles the same
--       branch.
--
--       This is a fact about `CSG`, not about `CsgQ`, and would sit more naturally beside the operator
--       in `Csg/ReachOp.lean`; it is stated here to keep the change confined to one file.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L176-L183
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L176-L183

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

theorem Comp.CsgQ.reachOp_coe (C : CSG S A1 A2) (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (v : S → Set.Icc (0 : ℝ) 1) (s : S) :
    (((C.reachOp goal hr) v s : ℝ))
      = if goal s then 1 else C.stageValue s (fun s' => ((v s' : ℝ))) := by sorry
