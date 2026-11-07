-- Prove2me | Theorems.Thm_AaronsonAmbainis_Dual_cover_iff_packing
-- name    : AaronsonAmbainis.Dual.cover_iff_packing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:25:58.245694+00:00
-- url     : https://prove2.me/theorems/ef8affff-b22a-48cd-a104-4ee8cbdbf489
-- title:
--   Dual: cover iff packing
-- statement:
--   The packing hypothesis of `CoverDuality` is equivalent to its conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sanity.lean#L49-L55
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sanity.lean#L49-L55

import Definitions.Def_AaronsonAmbainis_Dual_Cover
import Definitions.Def_AaronsonAmbainis_Dual_RowAux
import Definitions.Def_AaronsonAmbainis_MainTheorem
import Definitions.Def_AaronsonAmbainis_Dual_Sanity
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Dual.cover_iff_packing (t : Finset ι → ℝ) (K : ℝ) :
    (∀ κ : Finset ι → ℝ, (∀ S, 0 ≤ κ S) →
        (∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) →
        ∑ S, κ S * t S ≤ K) ↔
    ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ K ∧ ∀ S : Finset ι, t S ≤ ∑ i ∈ S, a i := by sorry
