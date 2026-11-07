-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_neg_derivative_eval_zero_le
-- name    : AaronsonAmbainis.Row.neg_derivative_eval_zero_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:36:16.873523+00:00
-- url     : https://prove2.me/theorems/6ba88eb9-cd81-485b-944b-5ba874d4ccc3
-- title:
--   Row: neg derivative eval zero le
-- statement:
--   One-sided form: `-p'(0) ≤ D²` if `|p| ≤ 1` on `[0,2]` and `natDegree p ≤ D`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Markov.lean#L20-L39
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Markov.lean#L20-L39

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Row_Markov
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Polynomial

theorem AaronsonAmbainis.Row.neg_derivative_eval_zero_le (D : ℕ) (p : ℝ[X]) (hdeg : p.natDegree ≤ D)
    (hbnd : ∀ s : ℝ, 0 ≤ s → s ≤ 2 → |p.eval s| ≤ 1) :
    -(p.derivative.eval 0) ≤ (D : ℝ) ^ 2 := by sorry
