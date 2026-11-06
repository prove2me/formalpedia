-- Prove2me | Theorems.Thm_CanadaCTP_eq_8
-- name    : CanadaCTP.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:23:52.155955+00:00
-- url     : https://prove2.me/theorems/b4b7c6e5-0373-48ae-8233-51a99e370b6b
-- title:
--   Eq. (8), first inequality — $\mathbb E[\mathrm{Opt}]\ge\sum_{\ell\ge0}2^\ell(u^*_\ell-u^*_{\ell+1})$
-- statement:
--   For every CTP instance on a disjoint-path graph and every feasible policy $\pi$,
--   $$
--   \mathbb E[\pi]\ \ge\ \mu\sum_{\ell\ge0}2^\ell\,(u^*_\ell-u^*_{\ell+1}),
--   $$
--   since $u^*_\ell-u^*_{\ell+1}$ is the probability that the cost lies in $[2^\ell,2^{\ell+1})$ (rescaled), and a non-zero cost is at least $1$ after rescaling.
--
--   It is the lower half of the latency argument of Theorem 1.
--
--   **Formalization Note** The paper states (8) for Opt; it holds for every feasible policy, Opt being one of them. The factor $\mu$ returns to original units; the series is a sum in $[0,\infty]$. The equalities that follow in display (8) are a reindexing.
--
--   Differences from the source:
--   - generalization: E[Opt] → E[π] for every feasible policy π; reason: Opt is a feasible policy, so the statement specializes to the source
--   - reading: display (8): E[Opt] ≥ Σ 2^ℓ(u*_ℓ − u*_{ℓ+1}) = Σ 2^ℓu*_ℓ − Σ 2^{ℓ−1}u*_ℓ = u*_0 + ½Σ 2^ℓu*_ℓ → its first inequality; reason: the equalities are a reindexing of the series
--   - encoding: rescaled units → μ·Σ … in original units, sum in ℝ≥0∞; reason: same quantity
--   - encoding: probabilities and expected values of the whole (possibly unbounded) run → suprema over the horizon N of the N-step quantities, in ℝ≥0∞; reason: the events are absorbing and the costs non-decreasing in N, so the suprema are the limits, i.e. the same values
--   - generalization: disjoint-path graphs (graphs, union of internally vertex-disjoint s–t paths) → any k ≥ 1 paths with m_i ≥ 1 edges, parallel one-edge paths allowed (a multigraph); reason: every disjoint-path graph is such an instance, so the statement specializes to the source
--   - encoding: independent non-negative discrete finitely supported edge weights given explicitly; edges and paths indexed from 1 → EdgeDist: an explicit list of (value, probability) pairs with distinct values, values ≥ 0, probabilities > 0 summing to 1; edges Fin m, paths Fin k, indexed from 0; reason: Lean convention; the list is exactly the support, so every instance of the paper is represented and nothing else
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Eq. (8), p.19

import Mathlib
import Definitions.Def_CanadaCTP_Analysis

namespace CanadaCTP

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33), Eq. (8), p.19, first inequality: `E[Opt] ≥ Σ_{ℓ≥0} 2^ℓ·(u*_ℓ − u*_{ℓ+1})`, since a
non-zero cost is at least `1` after rescaling.

**Formalization Note.** Stated for every feasible policy `π` in place of Opt, in original units
(`μ·Σ …`); the series is an `ℝ≥0∞` sum. -/
theorem eq_8 (I : Inst) (hI : I.IsCTP) {Mem : Type} (π : Policy I Mem) (hπ : Feasible I π) :
    ENNReal.ofReal (mu I) * ∑' ℓ : ℕ, 2 ^ ℓ * ENNReal.ofReal (uStar I π ℓ - uStar I π (ℓ + 1)) ≤
      expCost I π := by sorry

end CanadaCTP
