-- Prove2me | Theorems.Thm_Comp_gfp_eq_coe_fixFrom
-- name    : Comp.gfp_eq_coe_fixFrom
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:12:05.35775+00:00
-- url     : https://prove2.me/theorems/e8add230-5b46-4d33-b18e-62a92c9bd635
-- title:
--   Comp: gfp eq coe fix From
-- statement:
--   **The greatest fixed point, from a loop and a check.** No iteration count: the loop ran until it
--       stopped, `gfp_le_coe_fixAux` says it did not overshoot, and `hfix` says where it stopped is
--       fixed.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L174-L181
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L174-L181

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
variable [Fintype S]

theorem Comp.gfp_eq_coe_fixFrom (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) (x : Finset S)
    (hx : F.gfp ≤ (↑x : Set S)) (hfix : f (fixFrom f x) = fixFrom f x) :
    F.gfp = (↑(fixFrom f x) : Set S) := by sorry
