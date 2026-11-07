-- Prove2me | Theorems.Thm_AaronsonAmbainis_Dual_empty_nonpos_of_packing
-- name    : AaronsonAmbainis.Dual.empty_nonpos_of_packing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:25:55.415265+00:00
-- url     : https://prove2.me/theorems/7c275e9b-d0cb-49e2-a6af-25dd4fed9ae0
-- title:
--   Dual: empty nonpos of packing
-- statement:
--   The side hypothesis `t ∅ ≤ 0` of `CoverDuality` follows from the packing hypothesis.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sanity.lean#L58-L63
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sanity.lean#L58-L63

import Definitions.Def_AaronsonAmbainis_Dual_Cover
import Definitions.Def_AaronsonAmbainis_Dual_RowAux
import Definitions.Def_AaronsonAmbainis_MainTheorem
import Definitions.Def_AaronsonAmbainis_Dual_Sanity
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Dual.empty_nonpos_of_packing (t : Finset ι → ℝ) (K : ℝ)
    (hpack : ∀ κ : Finset ι → ℝ, (∀ S, 0 ≤ κ S) →
        (∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) →
        ∑ S, κ S * t S ≤ K) : t ∅ ≤ 0 := by sorry
