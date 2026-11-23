-- Prove2me | Theorems.Thm_Csg_CSG_reachOp_lfp_eq_sSup_iterate
-- name    : Csg.CSG.reachOp_lfp_eq_sSup_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:03:17.835527+00:00
-- url     : https://prove2.me/theorems/7df91076-0d5a-42cd-8ca0-a228b8e09d38
-- title:
--   CSG: reach Op lfp eq s Sup iterate
-- statement:
--   **Stage 3, the payoff.** `(C.reachOp goal hr).lfp` -- Knaster-Tarski's least fixed point,
--       already available for free the moment `ReachOp.lean` typechecks -- is genuinely the limit of
--       the naive iterate sequence starting from `⊥`: Kleene's fixed-point theorem
--       (`fixedPoints.lfp_eq_sSup_iterate`), applicable now that `reachOp_ωScottContinuous` supplies its
--       hypothesis. This upgrades `VERIFICATION-FRAMEWORK.md`'s "numeric iterate, undiscounted" row from
--       open to done, with no computable convergence *rate* attached (Kleene's theorem gives none).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ReachConverge.lean#L181-L184
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ReachConverge.lean#L181-L184

import Definitions.Def_Csg_ReachOp
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.FixedPoints
import Mathlib.Order.OmegaCompletePartialOrder
import Definitions.Def_Csg_ReachConverge
set_option autoImplicit true
open Csg
open Csg.CSG
open OmegaCompletePartialOrder Filter Topology
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.reachOp_lfp_eq_sSup_iterate (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    (C.reachOp goal hr).lfp = ⨆ n, (C.reachOp goal hr)^[n] ⊥ := by sorry
