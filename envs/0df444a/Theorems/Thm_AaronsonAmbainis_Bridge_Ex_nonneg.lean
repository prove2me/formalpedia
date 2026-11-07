-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_Ex_nonneg
-- name    : AaronsonAmbainis.Bridge.Ex_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:12:04.227576+00:00
-- url     : https://prove2.me/theorems/101a3174-0af1-4f88-9740-d79332b66304
-- title:
--   Bridge: Ex nonneg
-- statement:
--   The Bridge construction uses the Ex nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L103-L104
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L103-L104

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.Ex_nonneg {N : ℕ} {F : (Fin N → Bool) → ℝ} (hF : ∀ X, 0 ≤ F X) : 0 ≤ Ex F := by sorry
