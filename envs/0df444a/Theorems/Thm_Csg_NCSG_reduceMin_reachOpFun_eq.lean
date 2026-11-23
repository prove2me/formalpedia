-- Prove2me | Theorems.Thm_Csg_NCSG_reduceMin_reachOpFun_eq
-- name    : Csg.NCSG.reduceMin_reachOpFun_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:17:05.963804+00:00
-- url     : https://prove2.me/theorems/dc483bd0-c908-4d57-9031-1b17b97bcad3
-- title:
--   NCSG: reduce Min reach Op Fun eq
-- statement:
--   The two reduced games' reachability step functions agree pointwise, at every continuation and
--       state -- the `goal`-state branch is trivially the same constant `1` on both sides, and the
--       other branch is `reduceMin_stageValue_eq` itself, read through the `Set.Icc (0:ℝ) 1` wrapper
--       via `Subtype.ext`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CoalitionComplementReach.lean#L64-L71
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CoalitionComplementReach.lean#L64-L71

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

theorem Csg.NCSG.reduceMin_reachOpFun_eq (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a, G.r s a = 0) (v : S → Set.Icc (0 : ℝ) 1) (s : S) :
    (G.reduceMax Cᶜ).reachOpFun goal (G.reduceMax_r_zero Cᶜ hr) v s =
      (G.reduceMin C).reachOpFun goal (G.reduceMin_r_zero C hr) v s := by sorry
