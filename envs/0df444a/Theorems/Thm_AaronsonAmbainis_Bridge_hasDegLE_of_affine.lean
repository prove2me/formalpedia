-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_hasDegLE_of_affine
-- name    : AaronsonAmbainis.Bridge.hasDegLE_of_affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:48:34.470727+00:00
-- url     : https://prove2.me/theorems/82fb9efc-8ea5-432c-849f-bffdc87726e3
-- title:
--   Bridge: has Deg LE of affine
-- statement:
--   An affine change of letter does not raise the degree.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/ZeroOne.lean#L57-L70
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/ZeroOne.lean#L57-L70

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.hasDegLE_of_affine {φ ψ : Bool → ℝ} {α β : ℝ} (hψ : ∀ b, ψ b = β * φ b + α)
    {f : Cube ι → ℝ} {d : ℕ} (h : HasDegLE ψ f d) : HasDegLE φ f d := by sorry
