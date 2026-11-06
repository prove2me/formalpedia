-- Prove2me | Theorems.Thm_CanadaCTP_theorem_3
-- name    : CanadaCTP.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:22:37.850058+00:00
-- url     : https://prove2.me/theorems/3399569e-ff04-40fd-bf1c-530be715cbb6
-- title:
--   Theorem 3 — ParallelTraveller runs in time $O((1+\max(\log|E|,\log M))\sum_i d_i\max(d_i,\log k))$
-- statement:
--   There is a constant $C$ such that for every CTP instance on a disjoint-path graph, on every run of ParallelTraveller (every realization of the weights, every outcome of its coins, after any number of steps) the number of operations performed so far is at most
--   $$
--   C\,\big(1+\max(\log|E|,\log M)\big)\sum_{i=1}^k d_i\max(d_i,\log k),
--   $$
--   where $d_i=\sum_j|\operatorname{supp}X^i_j|$ and $M$ is the largest realization after rescaling the least non-zero realization to $1$.
--
--   Together with the expected-cost bound it makes ParallelTraveller the polynomial-time algorithm of Theorem 1.
--
--   **Formalization Note** The count is the counter `ops` in the policy's memory: every counted operation of every step (the planning at the start of each phase, the coin flips, look-ups, moves and the walk back to $s$). If every realization is $0$, $M$ is taken to be $1$. $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: runs in time O(…) → ∃ C, for every run and every horizon N, the operation counter ops ≤ C·(…); reason: unit-cost operation count of the named policy; one C for all instances
--   - encoding: M = largest realization after rescaling the least non-zero realization to 1 → Mbig I = max 1 (largest value / μ); reason: equal to M whenever a non-zero realization exists; if all are 0 the paper's M = 0 and log M is undefined
--   - reading: "and hence polynomial in the input size" → not restated; reason: a remark: log|E| and log M are at most the bit length of the explicit input, which has no Lean encoding here since the inputs are real numbers; the explicit bound is the content
--   - generalization: disjoint-path graphs (graphs, union of internally vertex-disjoint s–t paths) → any k ≥ 1 paths with m_i ≥ 1 edges, parallel one-edge paths allowed (a multigraph); reason: every disjoint-path graph is such an instance, so the statement specializes to the source
--   - encoding: independent non-negative discrete finitely supported edge weights given explicitly; edges and paths indexed from 1 → EdgeDist: an explicit list of (value, probability) pairs with distinct values, values ≥ 0, probabilities > 0 summing to 1; edges Fin m, paths Fin k, indexed from 0; reason: Lean convention; the list is exactly the support, so every instance of the paper is represented and nothing else
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Theorem 3, p.6 (restated p.15); proof pp.15–16

import Mathlib
import Definitions.Def_CanadaCTP_ParallelTraveller

namespace CanadaCTP

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33), Theorem 3, p.6 (restated p.15, proof pp.15–16): ParallelTraveller runs in time
`O((1 + max(log |E|, log M))·Σᵢ dᵢ·max(dᵢ, log k))`, with one constant for all instances, on
every run (every realization of the weights, every outcome of its coins, every horizon).

**Formalization Note.** Time is the operation counter `ops` in the policy's memory: every counted
operation of every step so far (planning at the start of each phase, coin flips, look-ups, moves,
the walk back to `s`). `M = Mbig I` is the largest realization after rescaling the least non-zero
one to `1` (`1` if every realization is `0`); `log` is the natural logarithm. -/
theorem theorem_3 : ∃ C : ℝ, ∀ I : Inst, I.IsCTP → ∀ (ι : Realz I) (N : ℕ),
    ∀ cfg ∈ (lawN I (ptPolicy I) ι N).support,
      (cfg.mem.ops : ℝ) ≤ C * (1 + max (Real.log (nE I)) (Real.log (Mbig I))) *
        ∑ i, (dsz I i : ℝ) * max (dsz I i : ℝ) (Real.log I.k) := by sorry

end CanadaCTP
