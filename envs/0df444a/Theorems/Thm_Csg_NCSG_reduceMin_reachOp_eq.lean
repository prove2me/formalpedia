-- Prove2me | Theorems.Thm_Csg_NCSG_reduceMin_reachOp_eq
-- name    : Csg.NCSG.reduceMin_reachOp_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:17:10.458537+00:00
-- url     : https://prove2.me/theorems/9e95711a-a095-4d2f-a298-3ea5b79bbfed
-- title:
--   NCSG: reduce Min reach Op eq
-- statement:
--   **The payoff.** The two reduced games' reachability Bellman operators are the *same*
--       `OrderHom` on `S → Set.Icc (0:ℝ) 1` -- not merely operators with equal values, but literally
--       equal terms, via `OrderHom.ext` applied to `reduceMin_reachOpFun_eq`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CoalitionComplementReach.lean#L76-L82
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CoalitionComplementReach.lean#L76-L82

import Definitions.Def_Csg_CoalitionComplement
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_CoalitionComplementReach
import Theorems.Thm_Csg_NCSG_reduceMax_r_zero
import Theorems.Thm_Csg_NCSG_reduceMin_r_zero

set_option autoImplicit true
open Csg
open Csg.NCSG
variable {S Players : Type*} {A : Players → Type*}
  [Fintype S] [Fintype Players] [DecidableEq Players]
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
variable (C : Finset Players) (G : NCSG S Players A)

theorem Csg.NCSG.reduceMin_reachOp_eq (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a, G.r s a = 0) :
    (G.reduceMax Cᶜ).reachOp goal (G.reduceMax_r_zero Cᶜ hr) =
      (G.reduceMin C).reachOp goal (G.reduceMin_r_zero C hr) := by sorry
