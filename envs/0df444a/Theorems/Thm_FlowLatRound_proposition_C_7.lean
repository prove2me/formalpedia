-- Prove2me | Theorems.Thm_FlowLatRound_proposition_C_7
-- name    : FlowLatRound.proposition_C_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:58:33.378198+00:00
-- url     : https://prove2.me/theorems/94a4669b-e9d7-420c-bf0b-bacf4d3b638a
-- title:
--   Proposition C.7 — a birthday representation: $X\overset{d}{=}X\prime$ and $P(X=\ell)=\frac{1}{(\alpha)_{\ell+1}}\sum_{(i_1,\dots,i_\ell)}\big(\prod_ja_{i_j}\big)\big(\sum_j(a_{i_j}-1)\big)$
-- statement:
--   In the tilted configuration model with degrees $(g_i)$ ($n\ge2$) and cycle rank $d\ge2$, let $X$ be the length of the fundamental cycle of a uniformly random one of the $d$ non-tree edges. Partition $\alpha$ slots into groups of sizes $a_1,\dots,a_n$ ($a_i=g_i-1$), draw slots uniformly without replacement, and let $X'$ be the number of draws made before some group is drawn for the second time. Then $X$ and $X'$ have the same law, and for $1\le\ell\le n$
--   $$P(X=\ell)=\frac{1}{(\alpha)_{\ell+1}}\sum_{(i_1,\dots,i_\ell)\ \text{distinct}}\Big(\prod_{j=1}^\ell a_{i_j}\Big)\Big(\sum_{j=1}^\ell(a_{i_j}-1)\Big).\tag{12}$$
--
--   The exact law of short cycles is the key input of both bounds of Theorem 1.1.
--
--   Differences from the source:
--   - reading: a degree sequence (no restriction on n written in the statement) → 2 ≤ n; reason: Appendix C.4 defines the tilted model with degrees (g_i) for n ≥ 2 (p.26); this is the standing setting of the statement
--   - encoding: X and X′ have the same law → P(X = ℓ) = P(X′ = ℓ) for every ℓ ∈ ℕ; reason: laws on ℕ are equal iff their point masses are
--   - encoding: (a_{i_j} − 1) in (12) → computed in ℝ; reason: a_i = 0 gives −1, as in the source's integer arithmetic
--   - encoding: the tilted configuration model (P1)–(P3); edges of G(π) labeled by the pairs of π → processProb: the step probabilities of (P1)–(P3) summed over the outcomes producing (π, T); edges of G(π) enumerated by their smaller half-edge and oriented from it (pairLaw = marginal of π); reason: the law of the process itself; a relabeling or reorientation of edges is a signed coordinate permutation and changes no lattice, cell, τ or cycle length
--   - encoding: vertices [n] and edges labeled 1..m → Fin n and Fin m (0-indexed); reason: Lean convention; relabeling changes no instance
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), Proposition C.7, Eq. (12), p.26 (PDF 28); proof p.27 (PDF 29)

import Mathlib
import Definitions.Def_FlowLatRound_TiltedModel

namespace FlowLatRound

/-- Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027 submission,
sha256 35bd3e4b…aeac), Proposition C.7, Eq. (12), p.26 (PDF 28). A birthday representation: in the tilted
configuration model with degrees `(gᵢ)` (`n ≥ 2`) and `d ≥ 2`, let `X` be the length of the
fundamental cycle of a uniformly random non-tree edge, and let `X′` be the number of draws,
uniformly without replacement from `α` slots in groups of sizes `a₁, …, a_n`, made before some
group is drawn for the second time. Then `X` and `X′` have the same law, and for `1 ≤ ℓ ≤ n`
`P(X = ℓ) = (1/(α)_{ℓ+1}) Σ_{(i₁,…,i_ℓ) distinct} (Π_j a_{i_j}) (Σ_j (a_{i_j} − 1))`. -/
theorem proposition_C_7 {n : ℕ} (g : DegSeq n) (hn : 2 ≤ n) (hd : 2 ≤ g.cr) :
    (∀ ℓ : ℕ, g.cycleLenProb ℓ = g.birthdayProb ℓ) ∧
    ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ n →
      g.cycleLenProb ℓ = 1 / (g.alpha.descFactorial (ℓ + 1) : ℝ) *
        ∑ s : Fin ℓ ↪ Fin n, (∏ j, (g.a (s j) : ℝ)) * (∑ j, ((g.a (s j) : ℝ) - 1)) := by sorry

end FlowLatRound
