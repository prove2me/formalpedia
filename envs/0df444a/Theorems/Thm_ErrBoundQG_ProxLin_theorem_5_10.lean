-- Prove2me | Theorems.Thm_ErrBoundQG_ProxLin_theorem_5_10
-- name    : ErrBoundQG.ProxLin.theorem_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:33.369894+00:00
-- url     : https://prove2.me/theorems/6e203a0a-c759-44dd-a7e3-b31776a596c6
-- title:
--   Theorem 5.10, p. 20 — subdifferential subregularity and the prox-linear error bound are equivalent
-- statement:
--   Let $\varphi=g+h\circ c$ be the convex-composite problem with $h$ $L$-Lipschitz and $\nabla c$ $\beta$-Lipschitz. Let $\bar x$ be stationary and $t>0$. Subregularity at $(\bar x,0)$ of the paper's composite subdifferential $\partial\varphi$ and of the prox-gradient map $\mathcal G_t$ imply each other with explicit constants:
--
--   $$
--   \mathcal G_t\text{ subregular with }\hat l
--   \ \Longrightarrow\ \partial\varphi\text{ subregular with }2\hat l,
--   $$
--   $$
--   \partial\varphi\text{ subregular with }l
--   \ \Longrightarrow\ \mathcal G_t\text{ subregular with }(3L\beta t+2)l+2t.
--   $$
--
--   This identifies the local prox-linear error bound with a property of the composite subdifferential, without restricting the positive step size $t$.
--
--   **Formalization Note** The prox-linear map is represented by its argmin values; the subdifferential is exactly $\partial g(x)+\nabla c(x)^*\partial h(c(x))$, as defined on p. 13. The constants $L$ and $\beta$ are nonnegative bounds, and subregularity constants are positive.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 20, Theorem 5.10

import Mathlib
import Definitions.Def_ErrBoundQG_ProxLin_Setting

namespace ErrBoundQG.ProxLin

theorem theorem_5_10 {n m : ℕ}
    (g : En n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (hgc : LowerSemicontinuous g)
    (h : En m → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (c : En n → En m) (hc : ContDiff ℝ 1 c)
    (L β : ℝ) (hL : 0 ≤ L) (hβ : 0 ≤ β)
    (hhL : ∀ a b, |h a - h b| ≤ L * ‖a - b‖)
    (hcβ : ∀ x y, ‖fderiv ℝ c x - fderiv ℝ c y‖ ≤ β * ‖x - y‖)
    (xbar : En n) (hxbar : IsStationary g h c xbar)
    (t : ℝ) (ht : 0 < t) :
    (∀ lhat : ℝ,
      IsSubregularAt (proxGradMap g h c t) xbar 0 lhat →
      IsSubregularAt (subdiffPhi g h c) xbar 0 (2 * lhat)) ∧
    (∀ l : ℝ,
      IsSubregularAt (subdiffPhi g h c) xbar 0 l →
      IsSubregularAt (proxGradMap g h c t) xbar 0
        ((3 * L * β * t + 2) * l + 2 * t)) := by sorry

end ErrBoundQG.ProxLin
