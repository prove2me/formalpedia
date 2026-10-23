-- Prove2me | Theorems.Thm_CorrClusterExp_IBR_lemma_4_1
-- name    : CorrClusterExp.IBR.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:04.745478+00:00
-- url     : https://prove2.me/theorems/11b3c841-1e32-4136-922f-98c26eae5ee3
-- title:
--   Lemma 4.1, p. 17 — relaxation of (1): V^LB ≤ V^OPT
-- statement:
--   Let $0<q\le\tfrac12$ and let $w_1,\dots,w_n\ge 0$ be cluster sizes. Let $V^{\mathrm{OPT}}$ and $V^{\mathrm{LB}}$ be the optimal values of the min–max problems (1) (over experiments with marginals $q$) and (5) (over all correlation matrices). Then
--   $$
--   V^{\mathrm{LB}}\le V^{\mathrm{OPT}} .
--   $$
--   The relaxation (5) is what the paper's approximation analysis compares IBR experiments against.
--
--   Differences from the source:
--   - generalization: sizes sorted, $w_1\ge\dots\ge w_n$ (Remark 4.1) → any sizes $w\ge 0$; reason: the order of the clusters plays no role, and the sorted case is an instance.
-- source:
--   Candogan, Chen, Niazadeh, Correlated Cluster-Based Randomized Experiments: Robust Variance Minimization, SSRN 3852100 (version of March 22, 2023), p. 17, Lemma 4.1

import Mathlib
import Definitions.Def_CorrClusterExp_IBR_Setting

namespace CorrClusterExp.IBR

theorem lemma_4_1 (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (n : ℕ) (w : Fin n → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) :
    VLB w ≤ VOPT q w := by sorry

end CorrClusterExp.IBR
