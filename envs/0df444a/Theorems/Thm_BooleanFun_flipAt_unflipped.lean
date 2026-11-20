-- Prove2me | Theorems.Thm_BooleanFun_flipAt_unflipped
-- name    : BooleanFun.flipAt_unflipped
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:04:34.8516+00:00
-- url     : https://prove2.me/theorems/490c55b9-e83b-4ef2-bedf-95beb510769f
-- title:
--   Boolean Fun: flip At unflipped
-- statement:
--   Bits that are not the `i₀`th bits remain unchanged.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L260-L262
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L260-L262

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

theorem BooleanFun.flipAt_unflipped {i i₀ : Fin n} {x : Fin n → Fin 2} (h : i ≠ i₀) : flipAt i₀ x i = x i := by sorry
