-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_exists_monomial_weight_le
-- name    : AaronsonAmbainis.DetLow.exists_monomial_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:25:39.065202+00:00
-- url     : https://prove2.me/theorems/9e2237d2-add7-4831-aa31-866156d9c902
-- title:
--   Det Low: exists monomial weight le
-- statement:
--   The Det Low construction uses the exists monomial weight le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Corollary.lean#L26-L32
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Corollary.lean#L26-L32

import Definitions.Def_AaronsonAmbainis_DetLow_Main
import Definitions.Def_AaronsonAmbainis_DetLow_Corollary
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial

theorem AaronsonAmbainis.DetLow.exists_monomial_weight_le {ι : Type} [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool)
    (ℓ : ι → ℝ) (hℓ : ∀ j, 0 ≤ ℓ j) :
    ∃ m ∈ (agMatrix g).det.support,
      ∑ j, ℓ j * (m j : ℝ) ≤ ∑ j, ℓ j * (bdry g j : ℝ) := by sorry
