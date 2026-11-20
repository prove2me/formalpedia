-- Prove2me | Theorems.Thm_Aggmetrics_micro_eq_macro_iff
-- name    : Aggmetrics.micro_eq_macro_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:52:30.471982+00:00
-- url     : https://prove2.me/theorems/60cd7773-fa32-499d-9d68-1d924069d49d
-- title:
--   Aggmetrics: micro eq macro iff
-- statement:
--   **Micro = denominator-weighted macro.**
--
--   For per-class denominators `den : Fin m → ℝ` (all positive), pooling numerators and
--   denominators globally before dividing (`micro`) equals averaging the per-class ratios
--   (`macro`), *for every choice of per-class numerators*, if and only if all per-class
--   denominators are equal.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/Basic.lean#L32-L62
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/Basic.lean#L32-L62

import Mathlib
import Definitions.Def_Aggmetrics_Basic
set_option autoImplicit true
open Finset
open Aggmetrics

theorem Aggmetrics.micro_eq_macro_iff {m : ℕ} (hm : 0 < m) (den : Fin m → ℝ) (hden : ∀ j, 0 < den j) :
    (∀ num : Fin m → ℝ,
      (∑ j, num j) / (∑ j, den j) = (1 / (m : ℝ)) * ∑ j, num j / den j)
    ↔ (∀ i j, den i = den j) := by sorry
