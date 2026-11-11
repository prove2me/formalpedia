-- Prove2me | Theorems.Thm_FlowLatRound_eq_13
-- name    : FlowLatRound.eq_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:58:50.33953+00:00
-- url     : https://prove2.me/theorems/82e3b5a2-0d01-429e-8d36-a40445315adb
-- title:
--   Eq. (13) — $\mathbb E_G\,S(K_G)/V(K_G)=2d\,\mathbb E X^{-1/2}$ for every degree sequence with $d\ge2$
-- statement:
--   For every degree sequence ($n\ge2$) with cycle rank $d\ge2$,
--   $$\mathbb E_G\frac{S(K_G)}{V(K_G)}=2d\,\mathbb E\,X^{-1/2},\tag{13}$$
--   the expectation over the tilted configuration model, $K_G$ the Voronoi cell of $\Lambda_G$.
--
--   Differences from the source:
--   - reading: a degree sequence (no restriction on n written in the statement) → 2 ≤ n; reason: Appendix C.4 defines the tilted model with degrees (g_i) for n ≥ 2 (p.26); this is the standing setting of the statement
--   - encoding: volume V and surface area S of a convex body in H_G → Lebesgue measure in orthonormal coordinates of H_G (cellVol) and the Minkowski content lim_{s↓0}(V(K_s)−V(K))/s (cellSurf); reason: basis-independent normalization of Lebesgue measure; the Minkowski content equals the surface area of a convex body (Steiner formula, used in the proof of Lemma B.2)
--   - encoding: E_G over the tilted model → Σ_π P[π]·(S/V)(K_{G(π)}); reason: graphs outside the support have weight 0
--   - encoding: the tilted configuration model (P1)–(P3); edges of G(π) labeled by the pairs of π → processProb: the step probabilities of (P1)–(P3) summed over the outcomes producing (π, T); edges of G(π) enumerated by their smaller half-edge and oriented from it (pairLaw = marginal of π); reason: the law of the process itself; a relabeling or reorientation of edges is a signed coordinate permutation and changes no lattice, cell, τ or cycle length
--   - encoding: vertices [n] and edges labeled 1..m → Fin n and Fin m (0-indexed); reason: Lean convention; relabeling changes no instance
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), Eq. (13), p.27 (PDF 29)

import Mathlib
import Definitions.Def_FlowLatRound_TiltedModel

namespace FlowLatRound

/-- Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027 submission,
sha256 35bd3e4b…aeac), Eq. (13), p.27 (PDF 29): by Proposition 3.3 and Lemma 3.6, for every degree sequence
(`n ≥ 2`) with `d ≥ 2`, `E_G S(K_G)/V(K_G) = 2d E X^{−1/2}`, the expectation over the tilted
configuration model. -/
theorem eq_13 {n : ℕ} (g : DegSeq n) (hn : 2 ≤ n) (hd : 2 ≤ g.cr) :
    g.ESV = 2 * (g.cr : ℝ) * g.EXneg := by sorry

end FlowLatRound
