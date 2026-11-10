-- Prove2me | Theorems.Thm_CoarseMatching_LowerBound_lemma_4_3
-- name    : CoarseMatching.LowerBound.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:36:12.458972+00:00
-- url     : https://prove2.me/theorems/b582f936-e680-49e4-aa83-d4a578ecc406
-- title:
--   Lemma 4.3 — Small-communication XOR acceptance gap
-- statement:
--   There is an absolute $C>0$ such that for each $0<\gamma<1$ one can choose an integer $2\le t\le C/\gamma$ and a threshold $m_0\ge1$. For all $m\ge m_0$, every local randomized protocol for the specified $t$-fold Unique Disjointness game satisfies
--
--   $$\mathrm{cost}\le m^{1-\gamma}\quad\Longrightarrow\quad\mathrm{gap}\le m^{-4}.$$
--
--   The threshold depends on $\gamma$, not on the protocol. The gap is the absolute difference of acceptance probabilities conditional on the two target parities. There is no round bound. This is the source’s amplified distributional communication lower bound.
--
--   Differences from the source:
--   - encoding: randomized local two-party protocols → published binary-tree and tape primitives extended by public-coin-dependent tree choice, actual transmitted-bit costs, and Bob as final local output party; reason: public coins may choose the schedule without changing resource counts; arbitrary tape laws are retained, and swapping the arbitrary input domains handles Alice output without communication
--   - encoding: t=O(1/γ) and sufficiently large m → one absolute C followed by t≤C/γ and m₀(γ); reason: makes the source uniformity and nonvacuous asymptotic threshold explicit
--   - encoding: independent uniform promised subset pairs in disjoint universes → Fin (4m) in each indexed universe, uniform permutation orbits, and uniform parity-conditioned bits; reason: the permutation action is transitive with equal-size fibers; the laws are exactly the source conditional laws
--   - generalization: communicated output bit included in Section 4 resource bounds → Bob’s local output need not be transmitted or transcript-determined; reason: the proof of Lemma 4.3 uses local acceptance probabilities, the one-instance communication bound and Lemma 3.1, which allow local output; every source protocol is included at its original cost
-- source:
--   Gillat Kol, Even Coarse Matching Estimates Require Nearly Linear Streaming Space, STOC 2027 submission #1135 (October 2026), Lemma 4.3, printed p. 14 (PDF p. 15). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1135.pdf

import Definitions.Def_CoarseMatching_LowerBound_UniqueDisjointness

namespace CoarseMatching.LowerBound

/-- Gillat Kol, STOC 2027 submission #1135 (October 2026), Lemma 4.3,
printed p.14 / PDF p.15. One absolute C for the O(1/γ) choice; the threshold
precedes m and the protocol. No round restriction; conditional acceptance gap. -/
theorem lemma_4_3 : ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, 0 < γ → γ < 1 →
    ∃ t : ℕ, 2 ≤ t ∧ (t : ℝ) ≤ C/γ ∧
      ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
        ∀ π : Protocol (UDInput m t) (UDInput m t),
          CostOn (UDInputs m t) π ((m : ℝ)^(1-γ)) →
          udGap m t π ≤ (m : ℝ)^(-4 : ℝ) := by sorry

end CoarseMatching.LowerBound
