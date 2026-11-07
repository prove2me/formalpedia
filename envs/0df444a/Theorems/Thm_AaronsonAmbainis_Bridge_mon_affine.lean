-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_mon_affine
-- name    : AaronsonAmbainis.Bridge.mon_affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:48:38.627501+00:00
-- url     : https://prove2.me/theorems/ddabef08-14aa-41d6-8467-58aed9d2a4a4
-- title:
--   Bridge: mon affine
-- statement:
--   Expansion of a monomial after an affine change of letter `ψ = β φ + α`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/ZeroOne.lean#L40-L54
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/ZeroOne.lean#L40-L54

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.mon_affine {φ ψ : Bool → ℝ} {α β : ℝ} (hψ : ∀ b, ψ b = β * φ b + α) (S : Finset ι)
    (x : Cube ι) :
    mon ψ S x
      = ∑ T : Finset ι, if T ⊆ S then β ^ T.card * α ^ (S \ T).card * mon φ T x else 0 := by sorry
