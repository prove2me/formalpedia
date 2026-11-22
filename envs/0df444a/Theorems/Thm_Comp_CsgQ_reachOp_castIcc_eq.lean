-- Prove2me | Theorems.Thm_Comp_CsgQ_reachOp_castIcc_eq
-- name    : Comp.CsgQ.reachOp_castIcc_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:52:46.531937+00:00
-- url     : https://prove2.me/theorems/3f80ebba-7a1e-4412-9ccd-5ec5d4e56461
-- title:
--   Csg Q: reach Op cast Icc eq
-- statement:
--   Collected per-state equalities lift to an equality of carrier vectors. This is the only place
--       `Subtype.ext` is needed, and it is why everything above is stated about the coercion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L206-L214
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L206-L214

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

theorem Comp.CsgQ.reachOp_castIcc_eq (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) (goal : S → Prop) [DecidablePred goal]
    (v w : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1)
    (k0 : ∀ s, 0 ≤ w s) (k1 : ∀ s, w s ≤ 1)
    (hstep : ∀ s, ((((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)) (castIcc v h0 h1) s : ℝ))
      = ((w s : ℚ) : ℝ)) :
    ((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)) (castIcc v h0 h1) = castIcc w k0 k1 := by sorry
