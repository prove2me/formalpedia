-- Prove2me | Theorems.Thm_Comp_gfp_eq_coe_fixFrom_univ
-- name    : Comp.gfp_eq_coe_fixFrom_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:49:41.352468+00:00
-- url     : https://prove2.me/theorems/96930c1e-6730-425e-bff2-38241666173c
-- title:
--   Comp: gfp eq coe fix From univ
-- statement:
--   **The greatest fixed point of `F`, as a computed `Finset`.** `gfp_le_coe_fixAux` keeps the loop
--       above `F.gfp`, `fixFrom_univ_fixed` says it stopped, and `mono_of_coe` gets the monotonicity the
--       latter needs out of the bridge -- so `hf` is the whole of what this asks for.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L263-L267
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L263-L267

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
variable [Fintype S]

theorem Comp.gfp_eq_coe_fixFrom_univ (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) :
    F.gfp = (↑(fixFrom f Finset.univ) : Set S) := by sorry
