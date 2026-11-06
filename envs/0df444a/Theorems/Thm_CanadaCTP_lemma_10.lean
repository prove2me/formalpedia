-- Prove2me | Theorems.Thm_CanadaCTP_lemma_10
-- name    : CanadaCTP.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:23:36.60642+00:00
-- url     : https://prove2.me/theorems/49b7ef7d-2cdb-4bdd-9b08-eab42e4d2af4
-- title:
--   Lemma 10 — $u_\ell\le e^{-1}u_{\ell-1}+(1-e^{-1})u^*_\ell$
-- statement:
--   Let $I$ be a CTP instance on a disjoint-path graph and $\pi$ any feasible policy. For every phase $\ell\ge0$,
--   $$
--   u_\ell\ \le\ e^{-1}\,u_{\ell-1}+(1-e^{-1})\,u^*_\ell ,
--   $$
--   where $u_\ell$ is the probability that ParallelTraveller has not finished by the end of phase $\ell$ ($u_{-1}$: by the end of the preprocessing) and $u^*_\ell$ the probability that $\pi$ costs at least $2^\ell$ in rescaled units.
--
--   It is the per-phase progress bound behind the constant of Theorem 1.
--
--   **Formalization Note** The paper states the lemma for an optimal policy Opt. Its proof uses no property of Opt beyond reaching $t$, so it is stated for every feasible $\pi$, Opt being one of them. Thresholds are $2^\ell\mu$ in original units.
--
--   Differences from the source:
--   - generalization: u*_ℓ for an optimal adaptive policy Opt → u*_ℓ for every feasible randomized stateful policy π; reason: Opt is a feasible policy, so the statement specializes to the source; no optimal policy needs to exist
--   - encoding: thresholds 2^ℓ after rescaling → 2^ℓ·μ in original units; reason: same events
--   - encoding: probabilities and expected values of the whole (possibly unbounded) run → suprema over the horizon N of the N-step quantities, in ℝ≥0∞; reason: the events are absorbing and the costs non-decreasing in N, so the suprema are the limits, i.e. the same values
--   - generalization: disjoint-path graphs (graphs, union of internally vertex-disjoint s–t paths) → any k ≥ 1 paths with m_i ≥ 1 edges, parallel one-edge paths allowed (a multigraph); reason: every disjoint-path graph is such an instance, so the statement specializes to the source
--   - encoding: independent non-negative discrete finitely supported edge weights given explicitly; edges and paths indexed from 1 → EdgeDist: an explicit list of (value, probability) pairs with distinct values, values ≥ 0, probabilities > 0 summing to 1; edges Fin m, paths Fin k, indexed from 0; reason: Lean convention; the list is exactly the support, so every instance of the paper is represented and nothing else
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Lemma 10, p.16; proof pp.16–18; definitions of u_ℓ, u*_ℓ, u_{−1}, p.16

import Mathlib
import Definitions.Def_CanadaCTP_Analysis

namespace CanadaCTP

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33), Lemma 10, p.16 (proof pp.16–18): for every phase `ℓ ≥ 0`,
`u_ℓ ≤ e^{−1}·u_{ℓ−1} + (1 − e^{−1})·u*_ℓ`.

**Formalization Note.** `u*_ℓ` is formed for an arbitrary feasible policy `π` in place of the
paper's Opt (Opt is one of them); the proof uses no property of Opt but feasibility. -/
theorem lemma_10 (I : Inst) (hI : I.IsCTP) {Mem : Type} (π : Policy I Mem) (hπ : Feasible I π)
    (ℓ : ℕ) :
    uAlg I ℓ ≤ Real.exp (-1) * uAlg I ((ℓ : ℤ) - 1) + (1 - Real.exp (-1)) * uStar I π ℓ := by sorry

end CanadaCTP
