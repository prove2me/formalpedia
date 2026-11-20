-- Prove2me | Theorems.Thm_BooleanFun_fourier_convolution
-- name    : BooleanFun.fourier_convolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:05:59.058186+00:00
-- url     : https://prove2.me/theorems/b7bd6c63-703c-48e9-a6fb-a81ec4b7dd4a
-- title:
--   Boolean Fun: fourier convolution
-- statement:
--   Convolution theorem : the Walsh-Fourier transform turns convolution into pointwise product.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L632-L653
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L632-L653

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

theorem BooleanFun.fourier_convolution : 𝓕 (f ⋆ g) = (𝓕 f) * (𝓕 g) := by sorry
