-- Prove2me | Theorems.Thm_Comp_CsgQ_le_lfp_of_step
-- name    : Comp.CsgQ.le_lfp_of_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:52:32.840622+00:00
-- url     : https://prove2.me/theorems/22264898-a9d3-4775-84ff-950ebc51f4c5
-- title:
--   Csg Q: le lfp of step
-- statement:
--   **The payoff.** A certified step from a vector already known to be a lower bound yields another
--       lower bound on the reachability value. Chaining this from `⊥` -- whose base case is `bot_le`
--       together with `castIcc_zero` -- gives a sound lower bound after any number of computed steps,
--       with no contraction and no `ε`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L220-L229
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L220-L229

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Reach
import Theorems.Thm_OrderHom_le_lfp_of_step

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.le_lfp_of_step (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) (goal : S → Prop) [DecidablePred goal]
    (v w : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1)
    (k0 : ∀ s, 0 ≤ w s) (k1 : ∀ s, w s ≤ 1)
    (hv : castIcc v h0 h1 ≤ ((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)).lfp)
    (hstep : ∀ s, ((((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)) (castIcc v h0 h1) s : ℝ))
      = ((w s : ℚ) : ℝ)) :
    castIcc w k0 k1 ≤ ((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)).lfp := by sorry
