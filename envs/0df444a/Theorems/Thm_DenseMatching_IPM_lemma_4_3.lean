-- Prove2me | Theorems.Thm_DenseMatching_IPM_lemma_4_3
-- name    : DenseMatching.IPM.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:40:22.178189+00:00
-- url     : https://prove2.me/theorems/9664669d-7b39-406a-8f62-a489fc59543e
-- title:
--   Lemma 4.3, bounds (5)–(9) — the clipped direction: |E_clipped| ≤ √m and the descent/curvature bounds (computation-cost sentence: see HARD.md)
-- statement:
--   On $K_{n/2,n/2}$ ($n=2k\ge2^{20}$, $m=k^2$, $\eta=10^{-5}$), under the invariants of Figure 3 ($\nu\in(-1,1)^E$, $\psi(\nu)\le10^2m$, Equation (4) for the representatives $\bar\nu$), the clipped direction $\Delta\mu$, the clipping parameter $\theta$ and the sets $E_{\rm clipped}$, $E_{\rm rest}$ of Definition 4.2 satisfy
--   $$|E_{\rm clipped}|\le\sqrt m,\tag{5}$$
--   $$|\Delta\mu|^\top|\psi'(\bar\nu)|\ge\eta^2/\theta,\tag{6}$$
--   $$\|\psi'(\bar\nu)_{E_{\rm rest}}\|_2\le\eta/\theta,\tag{7}$$
--   $$\mathbb 1^\top_{E_{\rm rest}}\psi''(\bar\nu)\le10^2(\eta\sqrt m/\theta+m),\tag{8}$$
--   $$|\Delta\mu|^\top|\psi'(\bar\nu)|\ge\frac{\eta\,\psi(\nu)}{2\sqrt m}-5\eta\sqrt m.\tag{9}$$
--   These bounds feed the sparsity intensity (Lemma 4.4) and the drift bound (Lemma 4.5).
--
--   This item is the mathematical part of Lemma 4.3, bounds (5)–(9). The lemma's last sentence (the left-hand sides are bucket sums computed in $O(\log n)$ time, and $E_{\rm clipped}$ is enumerated in $O(|E_{\rm clipped}|)$) is a running-time claim about real-valued sums on the pointer machine; it is not stated here and is recorded in `HARD.md`.
--
--   Differences from the source:
--   - encoding: the complete bipartite graph K_{n/2,n/2} of Section 4 with n ≥ 2^20 (p. 26), m = n²/4 → vertices Fin k ⊕ Fin k, edges Fin k × Fin k oriented L → R, n = 2k with 2^19 ≤ k, m = k²; reason: same instances; n is even on K_{n/2,n/2}
--   - reading: 'under the invariants of Figure 3' / 'of the IPM algorithm' → explicit hypotheses ν ∈ (−1,1)^E, ψ(ν) ≤ 10²m and Equation (4) for the representatives ν̄; reason: p. 25: 'A statement made under the invariants of the IPM algorithm assumes ψ(ν) ≤ 10²m and Equation (4)'; the other invariants of Figure 3 concern objects (r, anchors, x) that do not occur in the statement
--   - encoding: θ ∈ [0, ∞] with 1/θ := 0 at θ = ∞ → clipTheta in ℝ≥0∞, 1/θ = (θ⁻¹).toReal; reason: same values; θ > 0 always
-- source:
--   Dai, Peng, Sleator, Stepin, Yang, Approaching Optimality for Dense Bipartite Matching, STOC 2027 submission (manuscript sha256 0bdeb447…), p. 29, Lemma 4.3, Equations (5)–(9)

import Mathlib
import Definitions.Def_DenseMatching_IPM_FlowLP

namespace DenseMatching.IPM

/-- Lemma 4.3, bounds (5)–(9) (p. 29). On `K_{n/2,n/2}` (`n = 2k ≥ 2^20`, `m = k²`), under the
invariants of Figure 3 (`ν ∈ (−1, 1)^E`, `ψ(ν) ≤ 10²m`, Equation (4) for the representatives
`ν̄`), the clipped direction `Δμ`, the clipping parameter `θ` and the sets `E_clipped`, `E_rest` of
Definition 4.2 (with `η = 10⁻⁵`) satisfy (5) `|E_clipped| ≤ √m`, (6) `|Δμ|⊤|ψ′(ν̄)| ≥ η²/θ`,
(7) `‖ψ′(ν̄)_{E_rest}‖₂ ≤ η/θ`, (8) `1⊤_{E_rest} ψ″(ν̄) ≤ 10²(η√m/θ + m)`,
(9) `|Δμ|⊤|ψ′(ν̄)| ≥ ηψ(ν)/(2√m) − 5η√m`. The lemma's last sentence (the bucket sums and their
O(log n) computation time) is not part of this item. -/
theorem lemma_4_3 (k : ℕ) (hk : 2 ^ 19 ≤ k) (ν νbar : KE k → ℝ) (hν : ∀ e, |ν e| < 1)
    (hψ : potential ν ≤ 10 ^ 2 * (k : ℝ) ^ 2) (hrep : RepresentativesClose eta ν νbar) :
    let m : ℝ := (k : ℝ) ^ 2
    ((clippedEdges eta νbar).card : ℝ) ≤ Real.sqrt m ∧
      eta ^ 2 * invTheta eta νbar ≤ descent eta νbar ∧
      Real.sqrt (∑ e ∈ restEdges eta νbar, dpsi (νbar e) ^ 2) ≤ eta * invTheta eta νbar ∧
      ∑ e ∈ restEdges eta νbar, ddpsi (νbar e) ≤
        10 ^ 2 * (eta * Real.sqrt m * invTheta eta νbar + m) ∧
      eta * potential ν / (2 * Real.sqrt m) - 5 * eta * Real.sqrt m ≤ descent eta νbar := by sorry

end DenseMatching.IPM
