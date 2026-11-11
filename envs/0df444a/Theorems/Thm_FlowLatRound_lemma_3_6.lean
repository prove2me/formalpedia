-- Prove2me | Theorems.Thm_FlowLatRound_lemma_3_6
-- name    : FlowLatRound.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:58:46.85212+00:00
-- url     : https://prove2.me/theorems/375db7a7-46fe-41cc-884b-8bc9476a0cf5
-- title:
--   Lemma 3.6 — joint law: every $(\pi,T)$ with $T$ a spanning tree of $G(\pi)$ has the same probability; $P[\pi]\propto\tau(G(\pi))$ and $T\mid\pi$ is uniform
-- statement:
--   In the tilted configuration model with degrees $(g_i)$, $n\ge2$ and cycle rank $d\ge1$:
--
--   1. there is $p>0$ such that every pair $(\pi,T)$, where $\pi$ is a pairing and $T$ a spanning tree of $G(\pi)$, is produced with probability exactly $p$, and no other pair is produced;
--   2. consequently
--   $$P[\pi]=\frac{\tau(G(\pi))}{\sum_{\pi'}\tau(G(\pi'))};$$
--   3. conditional on $\pi$ (with $P[\pi]>0$), $T$ is a uniform spanning tree of $G(\pi)$.
--
--   The tilt by $\tau$ is what makes the planted tree a uniform spanning tree of the random graph.
--
--   Differences from the source:
--   - generalization: degree q (q-regular model) → every degree sequence (g_i) with n ≥ 2 and d ≥ 1; reason: Appendix C.4 (p.26) states that the proof applies verbatim; the q-regular case is g ≡ q
--   - reading: every pair (π, T) with T a spanning tree is produced with the same probability → processProb = p > 0 on spanning trees and 0 otherwise; reason: the output T is always a spanning tree of G(π) (p.8: "a set of n − 1 of its pairs that form a spanning tree")
--   - encoding: P[π] ∝ τ(G(π)); T uniform given π → P[π] = τ/Σ τ and P[(π,T)]/P[π] = 1/τ for P[π] ≠ 0; reason: the normalized form of proportionality and conditioning
--   - encoding: the tilted configuration model (P1)–(P3); edges of G(π) labeled by the pairs of π → processProb: the step probabilities of (P1)–(P3) summed over the outcomes producing (π, T); edges of G(π) enumerated by their smaller half-edge and oriented from it (pairLaw = marginal of π); reason: the law of the process itself; a relabeling or reorientation of edges is a signed coordinate permutation and changes no lattice, cell, τ or cycle length
--   - encoding: vertices [n] and edges labeled 1..m → Fin n and Fin m (0-indexed); reason: Lean convention; relabeling changes no instance
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), Lemma 3.6, p.8 (PDF 10); degree sequences, Appendix C.4, p.26 (PDF 28)

import Mathlib
import Definitions.Def_FlowLatRound_TiltedModel

namespace FlowLatRound

/-- Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027 submission,
sha256 35bd3e4b…aeac), Lemma 3.6, p.8 (PDF 10), in the degree-sequence form of Appendix C.4, p.26 (PDF 28)
("The proof of Lemma 3.6 applies verbatim"). Joint law: in the tilted configuration model with
degrees `(gᵢ)`, `n ≥ 2`, `d ≥ 1`, every pair `(π, T)` of a pairing and a spanning tree of `G(π)` is
produced with the same probability `p > 0` (and no other pair is produced). Consequently
`P[π] = τ(G(π)) / Σ_{π'} τ(G(π'))`, and conditional on `π` the tree `T` is a uniform spanning tree
of `G(π)`. -/
theorem lemma_3_6 {n : ℕ} (g : DegSeq n) (hn : 2 ≤ n) (hd : 1 ≤ g.cr) :
    (∃ p : ℝ, 0 < p ∧ ∀ (π : g.Pairing) (T : Finset (Fin g.m)),
      g.processProb π T = if (g.graphOf π).IsSpanningTree T then p else 0) ∧
    (∀ π : g.Pairing,
      g.pairLaw π = ((g.graphOf π).tau : ℝ) / ∑ π' : g.Pairing, ((g.graphOf π').tau : ℝ)) ∧
    (∀ (π : g.Pairing) (T : Finset (Fin g.m)), g.pairLaw π ≠ 0 →
      (g.graphOf π).IsSpanningTree T →
        g.processProb π T / g.pairLaw π = 1 / ((g.graphOf π).tau : ℝ)) := by sorry

end FlowLatRound
