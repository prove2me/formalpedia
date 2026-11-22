-- Prove2me | Theorems.Thm_Comp_CsgQ_lfp_le_of_step
-- name    : Comp.CsgQ.lfp_le_of_step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:28:08.346028+00:00
-- url     : https://prove2.me/theorems/7fd7c315-8f6e-4207-a07d-108018209051
-- title:
--   Csg Q: lfp le of step
-- statement:
--   **The dual payoff.** A certified step from a vector already known to be an upper bound yields
--       another upper bound. Chaining from `⊤` -- base case `le_top` with `castIcc_one` -- gives a sound
--       upper bound after any number of computed steps, so a run produces the whole interval
--       `[lower, upper]` rather than one side of it.
--
--       The interval is sound at every step but not guaranteed to shrink: see `OrderHom.lfp_le_of_step`
--       on why that is a convergence question rather than a soundness one.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L238-L247
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L238-L247

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Reach
import Theorems.Thm_OrderHom_lfp_le_of_step

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.lfp_le_of_step (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) (goal : S → Prop) [DecidablePred goal]
    (v w : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1)
    (k0 : ∀ s, 0 ≤ w s) (k1 : ∀ s, w s ≤ 1)
    (hv : ((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)).lfp ≤ castIcc v h0 h1)
    (hstep : ∀ s, ((((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)) (castIcc v h0 h1) s : ℝ))
      = ((w s : ℚ) : ℝ)) :
    ((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)).lfp ≤ castIcc w k0 k1 := by sorry
