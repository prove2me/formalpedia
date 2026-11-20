-- Prove2me | Theorems.Thm_Aggmetrics_weighted_ratio_mixture
-- name    : Aggmetrics.weighted_ratio_mixture
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:52:35.904599+00:00
-- url     : https://prove2.me/theorems/5785852b-4e68-4e80-940b-26a08211ae66
-- title:
--   Aggmetrics: weighted ratio mixture
-- statement:
--   **Weighted-ratio mixture identity** (always true, no skew-invariance needed): pooling
--   numerators and denominators and taking one ratio equals the prevalence-weighted average of
--   the per-class ratios, where class `j`'s weight is its own share `den j / ∑ k, den k` of the
--   total denominator. This is the "always-true" half underlying `micro_eq_macro_iff` above,
--   stated as its own reusable fact — the mechanism behind Corollary 5's micro-mixture formula
--   below.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/Basic.lean#L111-L119
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/Basic.lean#L111-L119

import Mathlib
import Definitions.Def_Aggmetrics_Basic
set_option autoImplicit true
open Finset
open Aggmetrics

theorem Aggmetrics.weighted_ratio_mixture {m : ℕ} (hm : 0 < m) (num den : Fin m → ℝ)
    (hden : ∀ j, 0 < den j) :
    (∑ j, num j) / (∑ j, den j) = ∑ j, (den j / ∑ k, den k) * (num j / den j) := by sorry
