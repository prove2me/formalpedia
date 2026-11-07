-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_coeff_unit_mul
-- name    : AaronsonAmbainis.DetLow.coeff_unit_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:19:43.997655+00:00
-- url     : https://prove2.me/theorems/f0e6de47-261b-493c-b0cc-47ec51502fe9
-- title:
--   Det Low: coeff unit mul
-- statement:
--   Key computation: if every monomial of `q` has total degree at least that of `m`, then
--   `u * q` and `q` have the same coefficient at `m` (when `u` has constant coefficient `1`).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Unit.lean#L17-L49
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Unit.lean#L17-L49

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetLow_Unit
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial

theorem AaronsonAmbainis.DetLow.coeff_unit_mul {ι : Type} [Fintype ι] (u q : MvPolynomial ι ℤ)
    (hu : constantCoeff u = 1) (m : ι →₀ ℕ)
    (hm : ∀ m' ∈ q.support, ∑ i, m i ≤ ∑ i, m' i) :
    coeff m (u * q) = coeff m q := by sorry
