-- Prove2me | Theorems.Thm_BooleanFun_walsh_setAt_eq_ite
-- name    : BooleanFun.walsh_setAt_eq_ite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:04:21.187715+00:00
-- url     : https://prove2.me/theorems/766c39cf-1878-4211-b51c-24ac9c2bb37c
-- title:
--   Boolean Fun: walsh set At eq ite
-- statement:
--   The Boolean Fun construction uses the walsh set At eq ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L371-L384
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L371-L384

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}

theorem BooleanFun.walsh_setAt_eq_ite : χ S (setAt i v x) = ite (i ∈ S) ((-1) ^ v.val * χ (S \ {i}) x) (χ S x) := by sorry
