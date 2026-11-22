-- Prove2me | Theorems.Thm_Comp_lfp_eq_coe_fixFrom_empty
-- name    : Comp.lfp_eq_coe_fixFrom_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:49:36.62499+00:00
-- url     : https://prove2.me/theorems/654df92b-5177-4ad9-ae9e-5aea2226b43a
-- title:
--   Comp: lfp eq coe fix From empty
-- statement:
--   The dual, for a least fixed point computed from `∅`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L270-L273
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L270-L273

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
variable [Fintype S]

theorem Comp.lfp_eq_coe_fixFrom_empty (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) :
    F.lfp = (↑(fixFrom f ∅) : Set S) := by sorry
