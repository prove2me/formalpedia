-- Prove2me | Theorems.Thm_FlowLatRound_upper_bound_display
-- name    : FlowLatRound.upper_bound_display
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:59:06.840221+00:00
-- url     : https://prove2.me/theorems/9daeece3-a278-4bae-8198-c6c9ae3591b9
-- title:
--   Proof of Theorem 1.1, upper bound (p.9) — $\mathbb E\,S/V=2d\,\mathbb EX^{-1/2}\le4dn^{-1/4}$ and $\mathbb E\,\Phi\le2\sqrt2\,d\,n^{1/4}\le3d^{5/4}$
-- statement:
--   Take $q=4$ and $n=d-1$, so that $m=2n$ and the cycle rank is $d$, for any $d\ge3$. Then
--   $$\mathbb E_\pi\frac{S(K_{G(\pi)})}{V(K_{G(\pi)})}=2d\,\mathbb E X^{-1/2}\le4d\,n^{-1/4},\qquad \mathbb E\,\Phi(K_G)\le2\sqrt2\,d\,n^{1/4}\le3d^{5/4}.$$
--
--   This is the upper half of $\mathbb E\,\Phi=\Theta(d^{5/4})$ in Theorem 1.1.
--
--   Differences from the source:
--   - encoding: volume V and surface area S of a convex body in H_G → Lebesgue measure in orthonormal coordinates of H_G (cellVol) and the Minkowski content lim_{s↓0}(V(K_s)−V(K))/s (cellSurf); reason: basis-independent normalization of Lebesgue measure; the Minkowski content equals the surface area of a convex body (Steiner formula, used in the proof of Lemma B.2)
--   - encoding: E over the tilted 4-regular model on n = d − 1 vertices → Σ_π P[π]·(…) with the degree sequence reg4 (d − 1); reason: graphs outside the support have weight 0
--   - encoding: the tilted configuration model (P1)–(P3); edges of G(π) labeled by the pairs of π → processProb: the step probabilities of (P1)–(P3) summed over the outcomes producing (π, T); edges of G(π) enumerated by their smaller half-edge and oriented from it (pairLaw = marginal of π); reason: the law of the process itself; a relabeling or reorientation of edges is a signed coordinate permutation and changes no lattice, cell, τ or cycle length
--   - encoding: vertices [n] and edges labeled 1..m → Fin n and Fin m (0-indexed); reason: Lean convention; relabeling changes no instance
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), proof of Theorem 1.1, upper-bound display, p.9 (PDF 11)

import Mathlib
import Definitions.Def_FlowLatRound_TiltedModel

namespace FlowLatRound

/-- Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027 submission,
sha256 35bd3e4b…aeac), proof of Theorem 1.1, upper bound, display on p.9 (PDF 11): with `q = 4` and
`n = d − 1` (so `m = 2n` and cycle rank `d`), `E_π S(K_{G(π)})/V(K_{G(π)}) = 2d E X^{−1/2} ≤ 4d n^{−1/4}`
and `E Φ(K_G) ≤ √(n/2) · 4d n^{−1/4} = 2√2 d n^{1/4} ≤ 3 d^{5/4}`, for every `d ≥ 3`. -/
theorem upper_bound_display (d : ℕ) (hd : 3 ≤ d) :
    (reg4 (d - 1)).ESV = 2 * (d : ℝ) * (reg4 (d - 1)).EXneg ∧
    (reg4 (d - 1)).ESV ≤ 4 * (d : ℝ) * ((d : ℝ) - 1) ^ (-(1 / 4 : ℝ)) ∧
    (reg4 (d - 1)).EPhi ≤ 2 * Real.sqrt 2 * (d : ℝ) * ((d : ℝ) - 1) ^ (1 / 4 : ℝ) ∧
    (reg4 (d - 1)).EPhi ≤ 3 * (d : ℝ) ^ (5 / 4 : ℝ) := by sorry

end FlowLatRound
