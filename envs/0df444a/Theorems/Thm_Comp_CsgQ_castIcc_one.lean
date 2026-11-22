-- Prove2me | Theorems.Thm_Comp_CsgQ_castIcc_one
-- name    : Comp.CsgQ.castIcc_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:27:13.097502+00:00
-- url     : https://prove2.me/theorems/08772bf0-5298-4063-ad3c-88a7e5a2128c
-- title:
--   Csg Q: cast Icc one
-- statement:
--   The all-one rational vector packages to the top of the carrier, the starting point for a
--       downward chain.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L107-L111
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L107-L111

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

theorem Comp.CsgQ.castIcc_one (h0 : ∀ s, (0 : ℚ) ≤ (fun _ : S => (1 : ℚ)) s)
    (h1 : ∀ s, (fun _ : S => (1 : ℚ)) s ≤ 1) :
    castIcc (fun _ : S => (1 : ℚ)) h0 h1 = ⊤ := by sorry
