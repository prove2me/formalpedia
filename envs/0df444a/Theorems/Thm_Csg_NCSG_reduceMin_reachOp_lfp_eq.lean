-- Prove2me | Theorems.Thm_Csg_NCSG_reduceMin_reachOp_lfp_eq
-- name    : Csg.NCSG.reduceMin_reachOp_lfp_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:04:47.419338+00:00
-- url     : https://prove2.me/theorems/5408220c-4b0b-4c40-b0c8-51d0b86ba03b
-- title:
--   NCSG: reduce Min reach Op lfp eq
-- statement:
--   **The actual `n`-player theorem**, at the reachability fixed point: `⟨⟨C⟩⟩P_min =?[F goal]` and
--       `⟨⟨Cᶜ⟩⟩P_max =?[F goal]` are the *same* least fixed point, for any coalition `C` of any
--       `Players`-indexed game and any reward-free `NCSG` (`G.r ≡ 0`, the hypothesis every reachability
--       instance in this project already satisfies). Immediate from `reduceMin_reachOp_eq`: equal
--       `OrderHom`s have equal `.lfp`s by definition.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CoalitionComplementReach.lean#L89-L93
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CoalitionComplementReach.lean#L89-L93

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

theorem Csg.NCSG.reduceMin_reachOp_lfp_eq (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a, G.r s a = 0) :
    ((G.reduceMax Cᶜ).reachOp goal (G.reduceMax_r_zero Cᶜ hr)).lfp =
      ((G.reduceMin C).reachOp goal (G.reduceMin_r_zero C hr)).lfp := by sorry
