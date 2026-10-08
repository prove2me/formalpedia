-- Prove2me | Theorems.Thm_AdWordsMSVV_LowerBound_harmonic_sum_bound
-- name    : AdWordsMSVV.LowerBound.harmonic_sum_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:29.916262+00:00
-- url     : https://prove2.me/theorems/2dc43681-3470-423d-80fa-0f2146e195fd
-- title:
--   Proof of Theorem 9, p. 15 — Σ_{j=1}^{N} min{1, Σ_{i=1}^{j} 1/(N−i+1)} ≤ (1 − 1/e + δ)N for all large N
-- statement:
--   For every $\delta > 0$ there is $N_0$ such that for every $N \ge N_0$,
--   $$\sum_{j=1}^{N}\min\Big\{1,\ \sum_{i=1}^{j}\frac{1}{N-i+1}\Big\} \le \Big(1-\frac1e+\delta\Big)N.$$
--
--   This is the analytic step of the proof of Theorem 9: summing the per-bidder bounds over the $N$ positions gives at most a $(1-1/e)$ fraction of the optimum $N$, up to a lower-order error.
--
--   **Formalization Note** The paper writes "at most $N(1-1/e)$". Taken literally this is false for every $N$ (at $N=1$ the sum is $1$; the excess over $N(1-1/e)$ tends to about $0.316$), so the bound is stated asymptotically with a slack $\delta N$; no explicit error term is asserted, since the paper gives none.
-- source:
--   Mehta, Saberi, Vazirani, Vazirani, AdWords and generalized on-line matching, J. ACM (2007), DOI 10.1145/1284320.1284321, p. 15, proof of Theorem 9, last paragraph, second sentence

import Mathlib
import Definitions.Def_AdWordsMSVV_LowerBound_Setting

namespace AdWordsMSVV.LowerBound

open Finset

theorem harmonic_sum_bound :
    ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ j ∈ Icc 1 N, min 1 (∑ i ∈ Icc 1 j, 1 / ((N : ℝ) - i + 1))
        ≤ (1 - Real.exp (-1) + δ) * N := by sorry

end AdWordsMSVV.LowerBound
