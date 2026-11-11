-- Prove2me | Theorems.Thm_DenseMatching_IPM_lemma_4_4
-- name    : DenseMatching.IPM.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:40:21.235188+00:00
-- url     : https://prove2.me/theorems/a803ef53-7701-4efd-a332-378a80a2c653
-- title:
--   Lemma 4.4 — the sparsity intensity p^s of Equation (10) sums to O(√m)
-- statement:
--   There is an absolute constant $C$ such that the following holds. On $K_{n/2,n/2}$ ($n=2k\ge2^{20}$, $m=k^2$, $\eta=10^{-5}$, $\alpha=10^7$), under the invariants of Figure 3 ($\nu\in(-1,1)^E$, $\psi(\nu)\le10^2m$, Equation (4) for $\bar\nu$), for $\tilde f,\tilde\nu\in\mathbb R^E$ with $\|\tilde f\|_2\le10^2\eta$ and $\|\tilde\nu\|_2\le2\cdot10^2\eta$, the vector $p^s$ that is $1$ on $E_{\rm clipped}$ and is given on $E_{\rm rest}$ by Equation (10) (with $0/0=0$, $\log=\log_2$) satisfies
--   $$\sum_e p^s_e\le C\sqrt m.$$
--   It bounds the expected number of edges sampled by the five sparsity channels of a step.
--
--   Differences from the source:
--   - encoding: the complete bipartite graph K_{n/2,n/2} of Section 4 with n ≥ 2^20 (p. 26), m = n²/4 → vertices Fin k ⊕ Fin k, edges Fin k × Fin k oriented L → R, n = 2k with 2^19 ≤ k, m = k²; reason: same instances; n is even on K_{n/2,n/2}
--   - reading: 'under the invariants of Figure 3' / 'of the IPM algorithm' → explicit hypotheses ν ∈ (−1,1)^E, ψ(ν) ≤ 10²m and Equation (4) for the representatives ν̄; reason: p. 25: 'A statement made under the invariants of the IPM algorithm assumes ψ(ν) ≤ 10²m and Equation (4)'; the other invariants of Figure 3 concern objects (r, anchors, x) that do not occur in the statement
--   - encoding: θ ∈ [0, ∞] with 1/θ := 0 at θ = ∞ → clipTheta in ℝ≥0∞, 1/θ = (θ⁻¹).toReal; reason: same values; θ > 0 always
--   - encoding: log (all logarithms base 2, p. 7) → Real.logb 2; reason: the paper's convention
--   - encoding: Σ_e p^s_e = O(√m) → ∃ C : ℝ, placed before k and every vector, with Σ_e p^s_e ≤ C√m; reason: the O(·) is an absolute constant (the proof gives α²)
-- source:
--   Dai, Peng, Sleator, Stepin, Yang, Approaching Optimality for Dense Bipartite Matching, STOC 2027 submission (manuscript sha256 0bdeb447…), p. 30, Lemma 4.4

import Mathlib
import Definitions.Def_DenseMatching_IPM_FlowLP

namespace DenseMatching.IPM

/-- Lemma 4.4 (p. 30). There is an absolute constant `C` such that on `K_{n/2,n/2}`
(`n = 2k ≥ 2^20`, `m = k²`), under the invariants of Figure 3, for `f̃, ν̃ ∈ ℝ^E` with
`‖f̃‖₂ ≤ 10²η`, `‖ν̃‖₂ ≤ 2·10²η`, the sparsity intensity `pˢ` of Equation (10) satisfies
`∑_e pˢ_e ≤ C √m`. -/
theorem lemma_4_4 :
    ∃ C : ℝ, ∀ k : ℕ, 2 ^ 19 ≤ k → ∀ ν νbar ft νt : KE k → ℝ,
      (∀ e, |ν e| < 1) → potential ν ≤ 10 ^ 2 * (k : ℝ) ^ 2 →
      RepresentativesClose eta ν νbar →
      l2norm ft ≤ 10 ^ 2 * eta → l2norm νt ≤ 2 * 10 ^ 2 * eta →
      ∑ e, sparsityIntensity (2 * k) eta alpha νbar ft νt e ≤ C * Real.sqrt ((k : ℝ) ^ 2) := by sorry

end DenseMatching.IPM
