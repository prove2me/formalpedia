-- Prove2me | Theorems.Thm_Aggmetrics_micro_skew_mixture
-- name    : Aggmetrics.micro_skew_mixture
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:52:41.061603+00:00
-- url     : https://prove2.me/theorems/65d22584-75c4-4329-8456-e582f877caf7
-- title:
--   Aggmetrics: micro skew mixture
-- statement:
--   **Corollary 5, part 2 (micro-averaging under skew): the mixture formula.**
--
--   For a skew-invariant measure `M = g ∘ (rec, spec)`, applied per class to give
--   `tp j, fp j, fn j, tn j`, the *pooled* (micro) recall and specificity fed to `g` are
--   exactly the prevalence-weighted averages of the per-class recall/specificity — `M^micro`
--   is `g` applied to a *mixture*, not to the per-class values directly.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/Basic.lean#L127-L134
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/Basic.lean#L127-L134

import Mathlib
import Definitions.Def_Aggmetrics_Basic
set_option autoImplicit true
open Finset
open Aggmetrics

theorem Aggmetrics.micro_skew_mixture {m : ℕ} (hm : 0 < m) (g : ℝ → ℝ → ℝ)
    (tp fp fn tn : Fin m → ℝ)
    (htpfn : ∀ j, 0 < tp j + fn j) (hfptn : ∀ j, 0 < fp j + tn j) :
    g ((∑ j, tp j) / (∑ j, (tp j + fn j))) ((∑ j, tn j) / (∑ j, (fp j + tn j)))
    = g (∑ j, ((tp j + fn j) / ∑ k, (tp k + fn k)) * (tp j / (tp j + fn j)))
        (∑ j, ((fp j + tn j) / ∑ k, (fp k + tn k)) * (tn j / (fp j + tn j))) := by sorry
