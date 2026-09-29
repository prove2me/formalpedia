-- Prove2me | Theorems.Thm_FirstOrderOpt_ConvexTheory_kkt_necessary
-- name    : FirstOrderOpt.ConvexTheory.kkt_necessary
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:56:39.422978+00:00
-- url     : https://prove2.me/theorems/e0d3948a-0e8a-4591-a0b6-7e164ee62369
-- title:
--   Theorem 2.8(b) — KKT conditions are necessary under the restricted Slater condition
-- statement:
--   Let (2.3.16) be a convex program with $X$ closed convex, $f, g_1,\dots,g_m$ convex on $X$,
--   and $h_1,\dots,h_p$ affine (witnesses $w, b$). Suppose the **restricted Slater condition**
--   holds: there is $\bar x$ in the relative interior of $X$ with $g_i(\bar x) \le 0$, $h_j(\bar
--   x)=0$ for all constraints and $g_j(\bar x) < 0$ strictly (Lan's "for all nonlinear
--   constraints"; every inequality constraint here is taken as nonlinear, the general case of
--   §2.3). Let $x^*$ be optimal for (2.3.16), feasible, and a point at which $f, g_1,\dots,g_m$
--   are differentiable.
--
--   **Theorem 2.8(b), necessity direction.** Then there exist Lagrange multipliers $\lambda^*
--   \ge 0$ and $y^*$ satisfying the KKT stationarity and complementary-slackness conditions of
--   Theorem 2.8(a) at $x^*$.
--
--   Together with `kkt_sufficient`, this is Lan's "necessary and sufficient": under the
--   restricted Slater condition, KKT multipliers exist for $x^*$ if and only if $x^*$ is
--   optimal. This mission's goal theorem is the necessity direction, since it is the one that
--   draws on the full separation → duality → saddle-point chain (via `strong_duality` and
--   `saddle_point_necessary`); `kkt_sufficient` needs none of that machinery.
--
--   **Formalization Note.** The relative interior is Mathlib's `intrinsicInterior ℝ X`,
--   distinct from the plain `interior X` used in `strong_duality`/`saddle_point_necessary`'s
--   (non-restricted) Slater condition — using the wrong one changes which of 2.6/2.7(b) versus
--   2.8(b) is being proved. Treating every $g_i$ as "nonlinear" (requiring $g_i(\bar x)<0$
--   strictly, rather than only the genuinely nonlinear subset) is a strengthening of the
--   hypothesis relative to Lan's fully general statement, not a weakening of the conclusion;
--   §2.3 never actually splits $g$ into affine/nonlinear parts for problem (2.3.16), so this
--   matches every worked instance of the chapter.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 42, Theorem 2.8(b)

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

namespace FirstOrderOpt.ConvexTheory

open scoped Gradient

/-- Theorem 2.8(b) (KKT necessity under the restricted Slater condition). If (2.3.16) has a
point `x̄` in the relative interior of `X` that is feasible with every inequality constraint
strict there, and `x*` is optimal and differentiable, then `x*` admits KKT multipliers
`λ* ≥ 0, y*` satisfying stationarity and complementary slackness. -/
theorem kkt_necessary {n m p : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (w : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (h : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (hh : ∀ j x, h j x = inner ℝ (w j) x + b j)
    (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (hfconv : ConvexOn ℝ X f) (hgconv : ∀ i, ConvexOn ℝ X (g i))
    (barx : EuclideanSpace ℝ (Fin n)) (hbarx_ri : barx ∈ intrinsicInterior ℝ X)
    (hbarx_g : ∀ i, g i barx < 0) (hbarx_h : ∀ j, h j barx = 0)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X)
    (hfdiff : DifferentiableAt ℝ f xstar) (hgdiff : ∀ i, DifferentiableAt ℝ (g i) xstar)
    (hxstar_g : ∀ i, g i xstar ≤ 0) (hxstar_h : ∀ j, h j xstar = 0)
    (hxstar_opt : ∀ x ∈ X, (∀ i, g i x ≤ 0) → (∀ j, h j x = 0) → f xstar ≤ f x) :
    ∃ lamStar : Fin m → ℝ, ∃ yStar : Fin p → ℝ, (∀ i, 0 ≤ lamStar i) ∧
      (∇ f xstar) + (∑ i, lamStar i • ∇ (g i) xstar) + (∑ j, yStar j • w j) ∈
        normalCone X xstar ∧
      (∀ i, lamStar i * g i xstar = 0) := by sorry

end FirstOrderOpt.ConvexTheory
