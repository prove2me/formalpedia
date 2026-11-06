-- Prove2me | Theorems.Thm_BinaryQueryLB_lemma_2_8_b
-- name    : BinaryQueryLB.lemma_2_8_b
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:46:45.565673+00:00
-- url     : https://prove2.me/theorems/cb417465-7417-4be4-8923-792a67cd8466
-- title:
--   Lemma 2.8(b) — $\min_{\mathbb B_{2m}}f_W=f_W(q^*_W)=-h_W$, with quadratic growth
-- statement:
--   Let $m\ge1$, $W\in\mathcal W$, $p_W$ the point of $K_W$ closest to the origin and $h_W=\|p_W\|_2$. The point $q^*_W=-p_W/h_W$ satisfies
--   $$
--   \min_{\mathbb B_{2m}}f_W=f_W(q^*_W)=-h_W,
--   $$
--   that is, $q^*_W\in\mathbb B_{2m}$, $f_W(q^*_W)=-h_W$ and $f_W\ge-h_W$ on $\mathbb B_{2m}$, and
--   $$
--   f_W(q)+h_W\ge\frac{h_W}{2}\,\|q-q^*_W\|_2^2\qquad\text{for every }q\in\mathbb B_{2m}.
--   $$
--   Here $\mathbb B_{2m}$ is the closed Euclidean unit ball of $\mathbb R^{2m}$.
--
--   The growth inequality turns near-optimality into closeness to $q^*_W$.
--
--   Differences from the source:
--   - encoding: m = ⌊d/2⌋ with d ≥ 2 → any m ≥ 1; reason: every m ≥ 1 equals ⌊2m/2⌋, so the instances are the same
--   - encoding: p_W, the point of K_W closest to the origin, and h_W = ∥p_W∥₂ → every point p of K_W of least norm, with h_W = ‖p‖; reason: there is exactly one such point
--   - encoding: min_{B_{2m}} f_W = f_W(q*_W) = −h_W → q*_W ∈ B_{2m}, f_W(q*_W) = −h_W, and f_W ≥ −h_W on B_{2m}; reason: the meaning of an attained minimum
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Lemma 2.8(b), p.13

import Mathlib
import Definitions.Def_BinaryQueryLB_KW
import Definitions.Def_BinaryQueryLB_IsMinNormPoint
import Definitions.Def_BinaryQueryLB_Wset
import Definitions.Def_BinaryQueryLB_fW

namespace BinaryQueryLB

/-- **Lemma 2.8(b) (Geometry of the minimizer).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Lemma 2.8(b), p.13: "The point
`q*_W = −p_W/h_W` satisfies `min_{B_{2m}} f_W = f_W(q*_W) = −h_W`, and
`f_W(q) + h_W ≥ (h_W/2)∥q − q*_W∥₂²` for every `q ∈ B_{2m}`."

Here `p_W` is the point of `K_W` closest to the origin and `h_W = ∥p_W∥₂`.

**Formalization Note.** "`min_{B_{2m}} f_W = f_W(q*_W) = −h_W`" is stated as: `q*_W ∈ B_{2m}`,
`f_W(q*_W) = −h_W`, and `f_W ≥ −h_W` on `B_{2m}` (the closed Euclidean unit ball of ℝ^{2m}).
`m ≥ 1`; every least-norm point `p` of `K_W` is allowed. -/
theorem lemma_2_8_b (m : ℕ) (hm : 1 ≤ m) (W : Fin m → EuclideanSpace ℝ (Fin m)) (hW : W ∈ Wset m)
    (p : PtSpace m) (hp : IsMinNormPoint (KW W) p) :
    (-(‖p‖⁻¹ • p)) ∈ Metric.closedBall (0 : PtSpace m) 1 ∧
      fW W (-(‖p‖⁻¹ • p)) = -‖p‖ ∧
      (∀ q ∈ Metric.closedBall (0 : PtSpace m) 1, -‖p‖ ≤ fW W q) ∧
      ∀ q ∈ Metric.closedBall (0 : PtSpace m) 1,
        ‖p‖ / 2 * ‖q - (-(‖p‖⁻¹ • p))‖ ^ 2 ≤ fW W q + ‖p‖ := by sorry

end BinaryQueryLB
