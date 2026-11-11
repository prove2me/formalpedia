-- Prove2me | Theorems.Thm_FlowLatRound_theorem_3_9
-- name    : FlowLatRound.theorem_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:58:37.543826+00:00
-- url     : https://prove2.me/theorems/97e2db08-95fd-46b4-9f4e-05214184a3ec
-- title:
--   Theorem 3.9 — limit of tilted configuration models: $\frac{\sqrt m}{2}\,\mathbb E_G\frac{S(K_G)}{V(K_G)}\ge c\,d^{5/4}$
-- statement:
--   There is an absolute constant $c>0$ such that for every degree sequence ($n\ge2$) with cycle rank $d\ge2$, the tilted configuration model satisfies
--   $$\frac{\sqrt m}{2}\,\mathbb E_G\frac{S(K_G)}{V(K_G)}\ge c\,d^{5/4},$$
--   and in particular $\mathbb E\,\Phi(K_G)\ge c\,d^{5/4}$ if all degrees are even. (The proof gives $c=c_0/2^{1/4}$, $c_0=1/(1072\sqrt2)$.)
--
--   No degree sequence beats the exponent $5/4$ through the radius bound $\sqrt m/2$; for the 4-regular model this is the lower half of Theorem 1.1.
--
--   Differences from the source:
--   - reading: a degree sequence (no restriction on n written in the statement) → 2 ≤ n; reason: Appendix C.4 defines the tilted model with degrees (g_i) for n ≥ 2 (p.26); this is the standing setting of the statement
--   - encoding: volume V and surface area S of a convex body in H_G → Lebesgue measure in orthonormal coordinates of H_G (cellVol) and the Minkowski content lim_{s↓0}(V(K_s)−V(K))/s (cellSurf); reason: basis-independent normalization of Lebesgue measure; the Minkowski content equals the surface area of a convex body (Steiner formula, used in the proof of Lemma B.2)
--   - encoding: E over the tilted model → Σ_π P[π]·(…); reason: graphs outside the support have weight 0
--   - encoding: the tilted configuration model (P1)–(P3); edges of G(π) labeled by the pairs of π → processProb: the step probabilities of (P1)–(P3) summed over the outcomes producing (π, T); edges of G(π) enumerated by their smaller half-edge and oriented from it (pairLaw = marginal of π); reason: the law of the process itself; a relabeling or reorientation of edges is a signed coordinate permutation and changes no lattice, cell, τ or cycle length
--   - encoding: vertices [n] and edges labeled 1..m → Fin n and Fin m (0-indexed); reason: Lean convention; relabeling changes no instance
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), Theorem 3.9, p.10 (PDF 12); proof p.28 (PDF 30)

import Mathlib
import Definitions.Def_FlowLatRound_TiltedModel

namespace FlowLatRound

/-- Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027 submission,
sha256 35bd3e4b…aeac), Theorem 3.9, p.10 (PDF 12); proof p.28 (PDF 30). Limit of tilted configuration
models: there is an absolute constant `c > 0` such that for every degree sequence (`n ≥ 2`) with
cycle rank `d ≥ 2`, `(√m/2) E_G S(K_G)/V(K_G) ≥ c d^{5/4}`; in particular `E Φ(K_G) ≥ c d^{5/4}` if all
degrees are even. (The proof gives `c = c₀/2^{1/4}`, `c₀ = 1/(1072√2)`.) -/
theorem theorem_3_9 :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (g : DegSeq n), 2 ≤ n → 2 ≤ g.cr →
      c * (g.cr : ℝ) ^ (5 / 4 : ℝ) ≤ Real.sqrt (g.m : ℝ) / 2 * g.ESV ∧
      ((∀ i, Even (g.g i)) → c * (g.cr : ℝ) ^ (5 / 4 : ℝ) ≤ g.EPhi) := by sorry

end FlowLatRound
