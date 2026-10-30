-- Prove2me | Theorems.Thm_CorrClusterExp_IBR_lemma_4_2
-- name    : CorrClusterExp.IBR.lemma_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:07.736417+00:00
-- url     : https://prove2.me/theorems/b629e1b0-fb52-4d40-a2b4-756cc7bdfe41
-- title:
--   Lemma 4.2, p. 18 — max{w₁², ¼Σwᵢ²} ≤ V^LB ≤ V^OPT ≤ Σwᵢ²
-- statement:
--   Let $0<q\le\tfrac12$, $n\ge 1$, and let $w_1\ge w_2\ge\dots\ge w_n\ge 0$ be the sorted cluster sizes. Then
--   $$
--   \max\Big\{w_1^2,\ \frac14\sum_{i\in[n]}w_i^2\Big\}\le V^{\mathrm{LB}}\le V^{\mathrm{OPT}}\le\sum_{i\in[n]}w_i^2 .
--   $$
--   In particular the independent assignment, whose worst-case variance is $\sum_i w_i^2$, is a $4$-approximation.
--
--   **Formalization Note** $w_1$ is `w ⟨0, hn⟩` (0-based).
--
--   Differences from the source:
--   - encoding: $w_1$ → `w ⟨0, hn⟩` with $0<n$; reason: 0-based indexing; $w_1$ needs a first cluster.
-- source:
--   Candogan, Chen, Niazadeh, Correlated Cluster-Based Randomized Experiments: Robust Variance Minimization, SSRN 3852100 (version of March 22, 2023), p. 18, Lemma 4.2

import Mathlib
import Definitions.Def_CorrClusterExp_IBR_Setting

namespace CorrClusterExp.IBR

theorem lemma_4_2 (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (n : ℕ) (hn : 0 < n)
    (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : Antitone w) :
    max (w ⟨0, hn⟩ ^ 2) (1 / 4 * ∑ i, w i ^ 2) ≤ VLB w ∧
      VLB w ≤ VOPT q w ∧ VOPT q w ≤ ∑ i, w i ^ 2 := by sorry

end CorrClusterExp.IBR
