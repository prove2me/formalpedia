-- Prove2me | Theorems.Thm_BinaryQueryLB_lemma_2_9_c
-- name    : BinaryQueryLB.lemma_2_9_c
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:48:34.161577+00:00
-- url     : https://prove2.me/theorems/94fc5b7e-bbed-40a1-853c-08b2d8882fc3
-- title:
--   Lemma 2.9(c) — an $\varepsilon$-optimal $y$ has $\|(\bar y/R)^\circ-q^*_W\|_2^2\le 8\sqrt m\,\varepsilon/(MR)$
-- statement:
--   Let $d\ge2$, $R,M>0$, $m=\lfloor d/2\rfloor$, $W\in\mathcal W$, and let $q^*_W=-p_W/h_W$ as in Lemma 2.8. If $\varepsilon>0$ and $y\in X$ is $\varepsilon$-optimal for $F_W$, then $\hat q=(\bar y/R)^\circ$ satisfies
--   $$
--   \|\hat q-q^*_W\|_2^2\le\frac{8\sqrt m\,\varepsilon}{MR}.
--   $$
--
--   Every $\varepsilon$-optimal output therefore determines the minimizer $q^*_W$ to precision $O\big((\sqrt m\,\varepsilon/(MR))^{1/2}\big)$.
--
--   Differences from the source:
--   - encoding: m = ⌊d/2⌋ → m = d / 2 (natural-number division); reason: the same number
--   - encoding: p_W, the point of K_W closest to the origin, and h_W = ∥p_W∥₂ → every point p of K_W of least norm, with h_W = ‖p‖; reason: there is exactly one such point
--   - encoding: f(ŷ) − min_X f ≤ ε with ŷ ∈ X → ŷ ∈ X and f(ŷ) ≤ f(y) + ε for all y ∈ X; reason: the minimum over X is attained for the functions considered, so the two forms agree
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Lemma 2.9(c), p.14

import Mathlib
import Definitions.Def_BinaryQueryLB_FW__386b32
import Definitions.Def_BinaryQueryLB_radialProj
import Definitions.Def_BinaryQueryLB_Wset
import Definitions.Def_BinaryQueryLB_IsEpsOptimal
import Definitions.Def_BinaryQueryLB_KW
import Definitions.Def_BinaryQueryLB_IsMinNormPoint

namespace BinaryQueryLB

/-- **Lemma 2.9(c) (Box and ball).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Lemma 2.9(c), p.14: "For every `W ∈ 𝒲`: … (c) if `y ∈ X`
is ε-optimal for `F_W`, then `q̂ = (ȳ/R)°` satisfies `∥q̂ − q*_W∥₂² ≤ 8√m ε/(MR)`."

Here `q*_W = −p_W/h_W` with `p_W` the point of `K_W` closest to the origin and `h_W = ∥p_W∥₂`.

**Formalization Note.** `d ≥ 2`, `R, M > 0`, `ε > 0` (ε-optimality is defined for `ε > 0`),
`m = d / 2`; every least-norm point `p` of `K_W` is allowed. -/
theorem lemma_2_9_c (d : ℕ) (hd : 2 ≤ d) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (W : Fin (d / 2) → EuclideanSpace ℝ (Fin (d / 2))) (hW : W ∈ Wset (d / 2))
    (p : PtSpace (d / 2)) (hp : IsMinNormPoint (KW W) p) (ε : ℝ) (hε : 0 < ε)
    (y : EuclideanSpace ℝ (Fin d)) (hy : IsEpsOptimal d R (FW d R M W) ε y) :
    ‖radialProj (R⁻¹ • ybar d y) - (-(‖p‖⁻¹ • p))‖ ^ 2 ≤
      8 * Real.sqrt ((d / 2 : ℕ) : ℝ) * ε / (M * R) := by sorry

end BinaryQueryLB
