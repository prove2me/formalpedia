-- Prove2me | Theorems.Thm_Comp_CsgQ_castIcc_zero
-- name    : Comp.CsgQ.castIcc_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:27:09.916058+00:00
-- url     : https://prove2.me/theorems/0412a767-e2ea-4dd0-865b-b3ae09dce7bd
-- title:
--   Csg Q: cast Icc zero
-- statement:
--   The all-zero rational vector packages to the bottom of the carrier, which is the base case of
--       any chain of steps.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L99-L103
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L99-L103

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Reach
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S : Type*}

theorem Comp.CsgQ.castIcc_zero (h0 : ∀ s, (0 : ℚ) ≤ (fun _ : S => (0 : ℚ)) s)
    (h1 : ∀ s, (fun _ : S => (0 : ℚ)) s ≤ 1) :
    castIcc (fun _ : S => (0 : ℚ)) h0 h1 = ⊥ := by sorry
