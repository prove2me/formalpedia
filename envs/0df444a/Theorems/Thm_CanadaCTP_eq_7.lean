-- Prove2me | Theorems.Thm_CanadaCTP_eq_7
-- name    : CanadaCTP.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:23:50.787422+00:00
-- url     : https://prove2.me/theorems/a6400aa5-6943-4d82-b975-c92c10e9ca62
-- title:
--   Eq. (7), first inequality — $\mathbb E[\mathrm{Alg}]\le\sum_{\ell\ge0}u_{\ell-1}2^{\ell+1}$
-- statement:
--   For every CTP instance on a disjoint-path graph,
--   $$
--   \mathbb E[\mathrm{Alg}]\ \le\ \mu\sum_{\ell\ge0}u_{\ell-1}\,2^{\ell+1},
--   $$
--   where $\mathrm{Alg}$ is ParallelTraveller and $\mu$ the rescaling factor: phase $\ell$ is entered with probability $u_{\ell-1}$ and then costs at most $2^{\ell+1}$ in rescaled units in expectation.
--
--   It is the upper half of the latency argument of Theorem 1.
--
--   **Formalization Note** The paper's units are rescaled; the factor $\mu$ returns to original units. The series is a sum in $[0,\infty]$. The two equalities that follow in display (7) are a reindexing of the series and the identity $u_{-1}=u^*_0$.
--
--   Differences from the source:
--   - reading: display (7): E[Alg] ≤ Σ u_{ℓ−1}2^{ℓ+1} = 2u_{−1} + Σ u_ℓ2^{ℓ+2} = 2u*_0 + 4Σ 2^ℓu_ℓ → its first inequality; reason: the equalities are a reindexing of the series and u_{−1} = u*_0; the milestone is the probabilistic step
--   - encoding: rescaled units → μ·Σ … in original units, sum in ℝ≥0∞; reason: same quantity
--   - encoding: probabilities and expected values of the whole (possibly unbounded) run → suprema over the horizon N of the N-step quantities, in ℝ≥0∞; reason: the events are absorbing and the costs non-decreasing in N, so the suprema are the limits, i.e. the same values
--   - generalization: disjoint-path graphs (graphs, union of internally vertex-disjoint s–t paths) → any k ≥ 1 paths with m_i ≥ 1 edges, parallel one-edge paths allowed (a multigraph); reason: every disjoint-path graph is such an instance, so the statement specializes to the source
--   - encoding: independent non-negative discrete finitely supported edge weights given explicitly; edges and paths indexed from 1 → EdgeDist: an explicit list of (value, probability) pairs with distinct values, values ≥ 0, probabilities > 0 summing to 1; edges Fin m, paths Fin k, indexed from 0; reason: Lean convention; the list is exactly the support, so every instance of the paper is represented and nothing else
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Eq. (7), p.19

import Mathlib
import Definitions.Def_CanadaCTP_Analysis

namespace CanadaCTP

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33), Eq. (7), p.19, first inequality: `E[Alg] ≤ Σ_{ℓ≥0} u_{ℓ−1}·2^{ℓ+1}`, from
`E[Alg_ℓ | τ_{ℓ−1}] ≤ 2^{ℓ+1}`.

**Formalization Note.** The paper's units are rescaled by `μ`; in original units the bound is
`μ·Σ_{ℓ≥0} u_{ℓ−1}·2^{ℓ+1}`. The series is an `ℝ≥0∞` sum. -/
theorem eq_7 (I : Inst) (hI : I.IsCTP) :
    expCost I (ptPolicy I) ≤
      ENNReal.ofReal (mu I) * ∑' ℓ : ℕ, ENNReal.ofReal (uAlg I ((ℓ : ℤ) - 1)) * 2 ^ (ℓ + 1) := by sorry

end CanadaCTP
