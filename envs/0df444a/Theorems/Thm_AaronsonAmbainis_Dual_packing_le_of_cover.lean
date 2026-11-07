-- Prove2me | Theorems.Thm_AaronsonAmbainis_Dual_packing_le_of_cover
-- name    : AaronsonAmbainis.Dual.packing_le_of_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:05:47.788837+00:00
-- url     : https://prove2.me/theorems/e3a5c923-8133-4540-b0cd-5a7acde2831c
-- title:
--   Dual: packing le of cover
-- statement:
--   Weak duality: a cover of mass at most `K` bounds the value of every fractional packing.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sanity.lean#L34-L46
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sanity.lean#L34-L46

import Definitions.Def_AaronsonAmbainis_Dual_Cover
import Definitions.Def_AaronsonAmbainis_Dual_RowAux
import Definitions.Def_AaronsonAmbainis_MainTheorem
import Definitions.Def_AaronsonAmbainis_Dual_Sanity
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Dual.packing_le_of_cover (t : Finset ι → ℝ) (K : ℝ) (a : ι → ℝ) (ha0 : ∀ i, 0 ≤ a i)
    (haK : ∑ i, a i ≤ K) (hcov : ∀ S : Finset ι, t S ≤ ∑ i ∈ S, a i)
    (κ : Finset ι → ℝ) (hκ : ∀ S, 0 ≤ κ S)
    (hload : ∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) :
    ∑ S, κ S * t S ≤ K := by sorry
