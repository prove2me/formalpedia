-- Prove2me | Theorems.Thm_CaiZhuInfo_Matrix_threshold_sum_bound
-- name    : CaiZhuInfo.Matrix.threshold_sum_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:15.782934+00:00
-- url     : https://prove2.me/theorems/a2bead86-fa97-470c-af6f-d841d151bc8a
-- title:
--   Lemma 4.3 — Threshold-sum bound
-- statement:
--   Let $n\ge1$ and let $R$ be any random variable taking values in $\{0,\dots,n\}$. Then
--   $$2^{-n}+\frac12\sum_{r=0}^{n-1}2^{-r-nP(R\ge r+1)}\le(8+4\sqrt2)2^{-H(R)-\mathbb ER}.$$
--   All tail probabilities and the mean use the given law of $R$; zero endpoint masses are allowed. This supplies the complete threshold estimate, including its endpoint term, for the convolution bound.
--
--   Differences from the source:
--   - encoding: a law supported on {0,...,n} and the sum from 0 to n-1 → PMF on Fin(n+1) and a sum over Fin n; reason: these finite index types represent exactly the stated support and summation domain
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), Lemma 4.3, (17), printed p.12 / PDF p.13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_LayerData

open MeasureTheory
open scoped Classical ENNReal

namespace CaiZhuInfo.Matrix

theorem threshold_sum_bound (n : ℕ) (hn : 0 < n) (P : PMF (Fin (n + 1))) :
    (2 : ℝ) ^ (-(n : ℝ)) + (1 / 2 : ℝ) *
      (∑ r : Fin n, (2 : ℝ) ^ (-(r.val : ℝ) - (n : ℝ) *
        mean P (fun k => if r.val + 1 ≤ k.val then 1 else 0))) ≤
      (8 + 4 * Real.sqrt 2) * (2 : ℝ) ^
        (-finiteEntropy P - mean P (fun k => (k.val : ℝ))) := by sorry

end CaiZhuInfo.Matrix
