-- Prove2me | Theorems.Thm_FlowLatRound_lemma_3_8
-- name    : FlowLatRound.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:58:57.919529+00:00
-- url     : https://prove2.me/theorems/fa1c6784-2a61-4c6f-9fca-24314522f8e3
-- title:
--   Lemma 3.8 — short cycles are rare: $P(X=\ell)\le\ell/n$ and $\mathbb E X^{-1/2}\le2n^{-1/4}$
-- statement:
--   In the setting of Proposition 3.7 (degree $q\ge3$, $n\ge2$, $qn$ even), $P(X=\ell)\le\ell/n$ for every $\ell$, and
--   $$\mathbb E\,X^{-1/2}\le2n^{-1/4}.$$
--
--   This bounds the negative half-moment that governs the boundary of the cell.
--
--   Differences from the source:
--   - encoding: the tilted configuration model (P1)–(P3); edges of G(π) labeled by the pairs of π → processProb: the step probabilities of (P1)–(P3) summed over the outcomes producing (π, T); edges of G(π) enumerated by their smaller half-edge and oriented from it (pairLaw = marginal of π); reason: the law of the process itself; a relabeling or reorientation of edges is a signed coordinate permutation and changes no lattice, cell, τ or cycle length
--   - encoding: vertices [n] and edges labeled 1..m → Fin n and Fin m (0-indexed); reason: Lean convention; relabeling changes no instance
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), Lemma 3.8, p.9 (PDF 11); proof p.27 (PDF 29)

import Mathlib
import Definitions.Def_FlowLatRound_TiltedModel

namespace FlowLatRound

/-- Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027 submission,
sha256 35bd3e4b…aeac), Lemma 3.8, p.9 (PDF 11); proof p.27 (PDF 29). Short cycles are rare: in the setting of
Proposition 3.7 (degree `q ≥ 3`, `n ≥ 2`, `qn` even), `P(X = ℓ) ≤ ℓ/n` for every `ℓ`, and
`E X^{−1/2} ≤ 2 n^{−1/4}`. -/
theorem lemma_3_8 (q n : ℕ) (hq : 3 ≤ q) (hn : 2 ≤ n) (he : Even (q * n)) :
    (∀ ℓ : ℕ, (regular n q (by omega) he).cycleLenProb ℓ ≤ (ℓ : ℝ) / n) ∧
    (regular n q (by omega) he).EXneg ≤ 2 * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by sorry

end FlowLatRound
