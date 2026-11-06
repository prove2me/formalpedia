-- Prove2me | Theorems.Thm_BinaryQueryLB_lemma_2_8_a
-- name    : BinaryQueryLB.lemma_2_8_a
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:46:41.561944+00:00
-- url     : https://prove2.me/theorems/572c492f-1e64-4aa7-83e9-dba36e6173d7
-- title:
--   Lemma 2.8, first clause and (a) — $p_W=(a\lambda,W^\top\lambda)$ and $a/\sqrt m\le h_W\le (a/\sqrt m)\sqrt{1+\Gamma^{-2}}$
-- statement:
--   Let $m\ge1$, $W\in\mathcal W$, and let $p_W$ be the point of $K_W=\operatorname{conv}\{v_1(W),\dots,v_m(W)\}$ closest to the origin, $h_W=\|p_W\|_2$. Then there is $\lambda$ in the standard simplex $\Delta_m=\{\lambda\in\mathbb R^m_{\ge0}:\sum_i\lambda_i=1\}$ with
--   $$
--   p_W=(a\lambda,\,W^\top\lambda),\qquad W^\top\lambda=\sum_i\lambda_i w_i,
--   $$
--   and
--   $$
--   \frac{a}{\sqrt m}\le h_W\le\frac{a}{\sqrt m}\sqrt{1+\Gamma^{-2}} .
--   $$
--
--   The norm $h_W$ is the depth of the minimum of $f_W$ over the unit ball (Lemma 2.8(b)), and these bounds fix it up to a factor $1+O(\Gamma^{-2})$.
--
--   Differences from the source:
--   - encoding: m = ⌊d/2⌋ with d ≥ 2 → any m ≥ 1; reason: every m ≥ 1 equals ⌊2m/2⌋, so the instances are the same
--   - encoding: p_W, the point of K_W closest to the origin, and h_W = ∥p_W∥₂ → every point p of K_W of least norm, with h_W = ‖p‖; reason: there is exactly one such point
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Lemma 2.8, p.13

import Mathlib
import Definitions.Def_BinaryQueryLB_KW
import Definitions.Def_BinaryQueryLB_IsMinNormPoint
import Definitions.Def_BinaryQueryLB_Wset
import Definitions.Def_BinaryQueryLB_aConst
import Definitions.Def_BinaryQueryLB_GammaConst

namespace BinaryQueryLB

/-- **Lemma 2.8, first clause and (a) (Geometry of the minimizer).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Lemma 2.8, p.13: "Let
`W ∈ 𝒲`. There is `λ ∈ ∆_m` with `p_W = (aλ, W⊤λ)`, and the following hold. (a)
`a/√m ≤ h_W ≤ (a/√m)√(1 + Γ^{−2})`."

Here `K_W = conv{v_1(W), …, v_m(W)}`, `p_W` is the point of `K_W` closest to the origin,
`h_W = ∥p_W∥₂`, `∆_m` is the standard simplex and `W⊤λ = Σ_i λ_i w_i`.

**Formalization Note.** `m ≥ 1` (it is `⌊d/2⌋` with `d ≥ 2`); the statement holds for every point
`p` of `K_W` of least norm (there is exactly one). `(aλ, W⊤λ)` is `VRAccelCLT.stack (a • λ) (Σ_i λ_i • w_i)`. -/
theorem lemma_2_8_a (m : ℕ) (hm : 1 ≤ m) (W : Fin m → EuclideanSpace ℝ (Fin m)) (hW : W ∈ Wset m)
    (p : PtSpace m) (hp : IsMinNormPoint (KW W) p) :
    (∃ lam ∈ stdSimplex ℝ (Fin m),
        p = VRAccelCLT.stack (aConst • WithLp.toLp 2 lam) (∑ i, lam i • W i)) ∧
      aConst / Real.sqrt m ≤ ‖p‖ ∧
      ‖p‖ ≤ aConst / Real.sqrt m * Real.sqrt (1 + GammaConst ^ (-2 : ℤ)) := by sorry

end BinaryQueryLB
