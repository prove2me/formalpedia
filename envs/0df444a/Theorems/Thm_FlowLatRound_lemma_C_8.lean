-- Prove2me | Theorems.Thm_FlowLatRound_lemma_C_8
-- name    : FlowLatRound.lemma_C_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:58:45.321067+00:00
-- url     : https://prove2.me/theorems/f4aa8a8f-a048-4481-99ce-c6594e333a27
-- title:
--   Lemma C.8 — $S_2\ge4d-4$ and $\mathbb EX^{-1/2}\ge c_0S_2^{1/4}/\sqrt\alpha$, $c_0=1/(1072\sqrt2)$
-- statement:
--   For every degree sequence ($n\ge2$) with cycle rank $d\ge2$, with $a_i=g_i-1$, $\alpha=\sum_ia_i$ and $S_2=\sum_ia_i(a_i-1)$,
--   $$S_2\ge4d-4\qquad\text{and}\qquad\mathbb E\,X^{-1/2}\ge\frac{c_0\,S_2^{1/4}}{\sqrt\alpha},\qquad c_0=\frac{1}{1072\sqrt2}.$$
--
--   This is the second-moment lower bound behind Theorem 3.9.
--
--   Differences from the source:
--   - reading: a degree sequence (no restriction on n written in the statement) → 2 ≤ n; reason: Appendix C.4 defines the tilted model with degrees (g_i) for n ≥ 2 (p.26); this is the standing setting of the statement
--   - encoding: the tilted configuration model (P1)–(P3); edges of G(π) labeled by the pairs of π → processProb: the step probabilities of (P1)–(P3) summed over the outcomes producing (π, T); edges of G(π) enumerated by their smaller half-edge and oriented from it (pairLaw = marginal of π); reason: the law of the process itself; a relabeling or reorientation of edges is a signed coordinate permutation and changes no lattice, cell, τ or cycle length
--   - encoding: vertices [n] and edges labeled 1..m → Fin n and Fin m (0-indexed); reason: Lean convention; relabeling changes no instance
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), Lemma C.8, p.28 (PDF 30)

import Mathlib
import Definitions.Def_FlowLatRound_TiltedModel

namespace FlowLatRound

/-- Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027 submission,
sha256 35bd3e4b…aeac), Lemma C.8, p.28 (PDF 30). For every degree sequence (`n ≥ 2`) with `d ≥ 2`, with
`aᵢ = gᵢ − 1`, `α = Σ aᵢ` and `S₂ = Σ aᵢ(aᵢ − 1)`: `S₂ ≥ 4d − 4` and
`E X^{−1/2} ≥ c₀ S₂^{1/4} / √α` for the absolute constant `c₀ = 1/(1072√2)`. -/
theorem lemma_C_8 {n : ℕ} (g : DegSeq n) (hn : 2 ≤ n) (hd : 2 ≤ g.cr) :
    4 * (g.cr : ℝ) - 4 ≤ g.S2 ∧
    1 / (1072 * Real.sqrt 2) * g.S2 ^ (1 / 4 : ℝ) / Real.sqrt (g.alpha : ℝ) ≤ g.EXneg := by sorry

end FlowLatRound
