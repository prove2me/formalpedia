-- Prove2me | Theorems.Thm_Comp_mono_of_coe
-- name    : Comp.mono_of_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:54:27.680072+00:00
-- url     : https://prove2.me/theorems/0ccea51f-d551-439e-b35a-509d92b9cc3e
-- title:
--   Comp: mono of coe
-- statement:
--   Monotonicity is not a separate assumption: the bridge gives it, because `Finset.coe` is an
--       order embedding and `F` is an `OrderHom`. This is what keeps `gfp_eq_coe_fixFrom_univ` down to
--       a single hypothesis.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L139-L145
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L139-L145

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
omit [DecidableEq S]

theorem Comp.mono_of_coe (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) : Monotone f := by sorry
