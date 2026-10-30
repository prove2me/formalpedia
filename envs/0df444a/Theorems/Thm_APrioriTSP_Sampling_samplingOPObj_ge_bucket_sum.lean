-- Prove2me | Theorems.Thm_APrioriTSP_Sampling_samplingOPObj_ge_bucket_sum
-- name    : APrioriTSP.Sampling.samplingOPObj_ge_bucket_sum
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-29T14:15:44.144957+00:00
-- url     : https://prove2.me/theorems/a0a7975e-f0f3-4760-97b3-86791227ab3d
-- title:
--   Inequality (12), p. 12 — the (Sampling-OP) objective dominates Σ_{i≤N} (1 − p)^{(i+1/2)b} B_i
-- statement:
--   Let $0<p<1$, let $b$ be an odd positive integer, and let $C=(C_i)_{i\ge1}$ satisfy $C_i\ge0$ (6) and $C_{i+j}\le C_i+C_j$ (7) for all $i,j\ge 1$. Let $B_i=\sum_{j=\max\{1,\,ib-(b-1)/2\}}^{ib+(b-1)/2}C_j$ be the buckets (9). Then for every $N\in\mathbb N$
--   $$\sum_{i=0}^{N}(1-p)^{(i+\frac12)b}\,B_i\ \le\ \sum_{i=1}^{\infty}(1-p)^{i-1}C_i .$$
--
--   This is inequality (12) of the paper, which bounds the objective of (Sampling-OP) from below by a finite expression in the buckets; it is the second ingredient in the proof of Lemma 15, where it is combined with $(1-\beta/b)^{(i+\frac12)b}\to e^{-(i+\frac12)\beta}$ as $b\to\infty$.
--
--   **Formalization Note** The right-hand side is `samplingOPObj p C` $=\sum_{i\ge0}(1-p)^iC_{i+1}$ (a `tsum`); condition (7) makes the series summable. The exponent $(i+\frac12)b$ is a real power.
-- source:
--   Blauth, Neuwohner, Puhlmann & Vygen, Improved guarantees for the a priori TSP, arXiv:2309.10663v1, p. 12, inequality (12)

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP

namespace APrioriTSP.Sampling

/-- (12), p. 12: for `0 < p < 1`, `b` odd and `C` satisfying (6) and (7),
`Σ_{i=0}^N (1 − p)^{(i + 1/2) b} B_i ≤ Σ_{i≥1} (1 − p)^{i−1} C_i` (right side shifted `i ↦ i + 1`). -/
theorem samplingOPObj_ge_bucket_sum (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (b : ℕ) (hb : Odd b)
    (C : ℕ → ℝ) (hC0 : ∀ i, 1 ≤ i → 0 ≤ C i)
    (hC : ∀ i j, 1 ≤ i → 1 ≤ j → C (i + j) ≤ C i + C j) (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), (1 - p) ^ ((((i : ℝ) + 1 / 2) * b)) * bucket b C i ≤
      samplingOPObj p C := by
  sorry

end APrioriTSP.Sampling
