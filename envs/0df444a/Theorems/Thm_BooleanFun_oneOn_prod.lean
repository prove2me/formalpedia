-- Prove2me | Theorems.Thm_BooleanFun_oneOn_prod
-- name    : BooleanFun.oneOn_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:59:18.580549+00:00
-- url     : https://prove2.me/theorems/c04901f9-8a23-41d1-b50e-e99771e5e44e
-- title:
--   Boolean Fun: one On prod
-- statement:
--   The Boolean Fun construction uses the one On prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Auxiliary.lean#L107-L114
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Auxiliary.lean#L107-L114

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_BooleanFun_Auxiliary
set_option autoImplicit false
open BooleanFun
open Finset Pi
variable {α : Type*} {β : Type*}
variable {s : Finset α}
variable {ι : Type*} [Fintype ι]
variable {κ : Type*}
variable {R : Type*} {M : Type*}
variable [Ring R] [AddCommGroup M] [Module R M]
noncomputable section
variable {p q : Prop}
open Classical

theorem BooleanFun.oneOn_prod {p : ι → Prop} : ∏ i, oneOn (p i) = oneOn (∀ i, p i) := by sorry
