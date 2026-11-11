-- Prove2me | Theorems.Thm_DenseMatching_IPM_lemma_4_15
-- name    : DenseMatching.IPM.lemma_4_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:40:01.547516+00:00
-- url     : https://prove2.me/theorems/1b94f0ff-2c5e-4687-ad0a-3b2c72d5b5a8
-- title:
--   Lemma 4.15 — an eligible state at µ ≤ 1/(10m) pins the min-cost perfect matching within 1 of −d⊤x
-- statement:
--   Work on $K_{n/2,n/2}$ ($n=2k\ge2^{20}$, $m=k^2$) with the demands $d$ and incidence matrix $B$ of §4. Let $(f,c,\mu)$ be eligible (Definition 4.1), $x\in\mathbb R^V$, and $r=B^\top f-d$. Then
--   $$g=f-\mathrm{Diag}(f/c)\,B\,(B^\top\mathrm{Diag}(f/c)B)^\dagger r$$
--   is a fractional perfect matching ($B^\top g=d$, $g\ge0$) with $(1-1.1\cdot10^{-4})f_e\le g_e\le(1+1.1\cdot10^{-4})f_e$ for every edge. If moreover $\mu\le1/(10m)$, then the minimum of $(c-Bx)^\top h$ over fractional perfect matchings $h$ exists, equals the minimum cost of a perfect matching under the costs $c-Bx$, and
--   $$-d^\top x\ \le\ \min\{(c-Bx)^\top h: B^\top h=d,\ h\ge0\}\ \le\ -d^\top x+1.2\,\mu m\ <\ -d^\top x+1.$$
--   This lemma turns the final state of the method into the exact optimum (Step 4 of Figure 4) and is used in the proof of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: the complete bipartite graph K_{n/2,n/2} of Section 4 with n ≥ 2^20 (p. 26), m = n²/4 → vertices Fin k ⊕ Fin k, edges Fin k × Fin k oriented L → R, n = 2k with 2^19 ≤ k, m = k²; reason: same instances; n is even on K_{n/2,n/2}
--   - encoding: ‖v‖²_{(B⊤Diag(f/c)B)†}, the Moore–Penrose pseudoinverse of the tracked Laplacian → v ⬝ᵥ (lapPinv *ᵥ v) of the published WGraph with weights f/c (pinvNormSq); reason: same object for f, c > 0, which every statement assumes
--   - encoding: 'the minimum cost min{(c − Bx)⊤f : B⊤f = d, f ≥ 0} … which equals the minimum cost of a perfect matching' → IsLeast of the set of fractional costs at minPerfectMatchingCost (minimum over permutations σ of Σ_i (c − Bx)_{(i,σ i)}), followed by the sandwich for that value; reason: states both that the minimum is attained and that it equals the perfect-matching minimum; perfect matchings of K_{k,k} are the permutations
-- source:
--   Dai, Peng, Sleator, Stepin, Yang, Approaching Optimality for Dense Bipartite Matching, STOC 2027 submission (manuscript sha256 0bdeb447…), p. 50, Lemma 4.15

import Mathlib
import Definitions.Def_EffResSparsify_Sampling_Defs
import Definitions.Def_DenseMatching_IPM_FlowLP

open Matrix

namespace DenseMatching.IPM

/-- Lemma 4.15 (p. 50). On `K_{n/2,n/2}` (`n = 2k ≥ 2^20`, `m = k²`), let `(f, c, μ)` be eligible,
`x ∈ ℝ^V` and `r = B⊤f − d`. Then `g = f − Diag(f/c) B (B⊤Diag(f/c)B)† r` is a fractional perfect
matching with `g ≈_{1.1·10⁻⁴} f` entrywise. If moreover `μ ≤ 1/(10m)`, the minimum of `(c − Bx)⊤h`
over fractional perfect matchings `h` exists and equals the minimum cost of a perfect matching under
`c − Bx`, and `−d⊤x ≤ min ≤ −d⊤x + 1.2μm < −d⊤x + 1`. -/
theorem lemma_4_15 (k : ℕ) (hk : 2 ^ 19 ≤ k) (f c : KE k → ℝ) (μ : ℝ) (hel : Eligible k f c μ)
    (x : KV k → ℝ) :
    let r := residual k f
    let g : KE k → ℝ := fun e => f e - f e / c e * (incK k *ᵥ pinvApply k f c r) e
    ((incK k)ᵀ *ᵥ g = demand k ∧ (∀ e, 0 ≤ g e) ∧
      ∀ e, (1 - 1.1 / 10 ^ 4) * f e ≤ g e ∧ g e ≤ (1 + 1.1 / 10 ^ 4) * f e) ∧
    (μ ≤ 1 / (10 * (k : ℝ) ^ 2) →
      let a : KE k → ℝ := c - incK k *ᵥ x
      IsLeast {v : ℝ | ∃ h : KE k → ℝ, (incK k)ᵀ *ᵥ h = demand k ∧ (∀ e, 0 ≤ h e) ∧ v = a ⬝ᵥ h}
          (minPerfectMatchingCost k a) ∧
        -(demand k ⬝ᵥ x) ≤ minPerfectMatchingCost k a ∧
        minPerfectMatchingCost k a ≤ -(demand k ⬝ᵥ x) + 1.2 * μ * (k : ℝ) ^ 2 ∧
        -(demand k ⬝ᵥ x) + 1.2 * μ * (k : ℝ) ^ 2 < -(demand k ⬝ᵥ x) + 1) := by sorry

end DenseMatching.IPM
