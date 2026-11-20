-- Prove2me | Theorems.Thm_Aggmetrics_micro_invariant_under_equal_rates
-- name    : Aggmetrics.micro_invariant_under_equal_rates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:52:46.270888+00:00
-- url     : https://prove2.me/theorems/6943d172-f131-4f1d-a1b3-188f4ee62e71
-- title:
--   Aggmetrics: micro invariant under equal rates
-- statement:
--   **Corollary 5's sensitivity boundary, made precise: equal per-class rates survive any
--   reweighting.** If every class has the *same* recall `r` and specificity `s`, the pooled
--   (micro) recall and specificity equal `r` and `s` too, for *any* positive per-class
--   denominators — `M^micro` is unaffected by class prevalence whenever the per-class rates
--   are equal. This is exactly the fact behind the collaborator's counterexample to the
--   unqualified, over-broad Corollary 8/10 in `papers/06-generalised-confusion/paper`: class
--   imbalance *alone* does not make a skew-invariant measure's micro-average
--   skew-*sensitive*.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/Basic.lean#L144-L161
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/Basic.lean#L144-L161

import Mathlib
import Definitions.Def_Aggmetrics_Basic
set_option autoImplicit true
open Finset
open Aggmetrics

theorem Aggmetrics.micro_invariant_under_equal_rates {m : ℕ} (hm : 0 < m)
    (tp fp fn tn : Fin m → ℝ) (r s : ℝ)
    (htpfn : ∀ j, 0 < tp j + fn j) (hfptn : ∀ j, 0 < fp j + tn j)
    (hrec : ∀ j, tp j / (tp j + fn j) = r) (hspec : ∀ j, tn j / (fp j + tn j) = s) :
    (∑ j, tp j) / (∑ j, (tp j + fn j)) = r ∧
    (∑ j, tn j) / (∑ j, (fp j + tn j)) = s := by sorry
