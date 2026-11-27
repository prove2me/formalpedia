-- Prove2me | Theorems.Thm_CubicNewton_Nonconvex_Supplement_theorem_10
-- name    : CubicNewton.Nonconvex.Supplement.theorem_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T08:14:37.209486+00:00
-- url     : https://prove2.me/theorems/bb03d155-4589-4318-b35a-333ee7bf9d21
-- title:
--   Theorem 10 — strong duality and exact duality gap (corrected: continuous boundary value)
-- statement:
--   Let $g\in\mathbb R^n$, let $H$ be a symmetric operator on $\mathbb R^n$ (possibly indefinite), and let $M>0$. With $v_u$, $v_l$, $\mathcal D$ and $h(r)=-(H+\frac{Mr}2I)^{-1}g$ as in Section 5.1,
--   $$\min_{h\in\mathbb R^n}v_u(h)=\sup_{r\in\mathcal D}v_l(r) .\qquad(5.2)$$
--   For any $r\in\mathcal D$ the direction $h(r)$ satisfies
--   $$0\le v_u(h(r))-v_l(r)=\frac M{12}\,(r+2\|h(r)\|)(\|h(r)\|-r)^2=\frac4{3M}\cdot\frac{r+2\|h(r)\|}{(r+\|h(r)\|)^2}\cdot v_l'(r)^2 .\qquad(5.3)$$
--   The supremum need not be attained in $\mathcal D$ (the boundary case $r=\frac2M(-\lambda_n(H))_+$), and $g=0$ is allowed. The nonconvex subproblem (5.1) that defines the cubic step is thus equivalent to a concave one-dimensional problem.
--
--   **Formalization Note** At $r=0$, $g=0$, and $H\succ0$, the quotient in the last expression of (5.3) is undefined as printed. The whole product with $v_l'(r)^2$ is assigned its continuous value $0$, fixed by the first factorization and the derivative formula on p. 199. The quotient alone has no finite continuous extension.
--
--   Differences from the source:
--   - encoding: min_h v_u(h) = sup_{r∈𝒟} v_l(r) → some h* minimizes v_u globally and v_u(h*) is the least upper bound (IsLUB) of v_l over 𝒟; reason: the min is attained; the sup is a least upper bound that need not be attained
--   - encoding: H symmetric; (H + (Mr/2)I)⁻¹ → ⟨Ha, b⟩ = ⟨a, Hb⟩; ContinuousLinearMap.inverse, the actual inverse for r ∈ 𝒟; reason: same objects
--   - correction: v_l′(r), and the quotient (r + 2‖h(r)‖)/(r + ‖h(r)‖)² at r = 0, g = 0 → deriv of v_l at r; the entire derivative-product expression has value 0 at r = 0, g = 0 (implemented by Lean real division); reason: the quotient alone diverges there; using v_l′(r) = (M/4)(‖h(r)‖² − r²), the full product extends continuously to the first factorization, whose value is 0; no source instance is excluded
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 198, Theorem 10, (5.2)–(5.3)

import Mathlib
import Definitions.Def_CubicNewton_Nonconvex_Supplement_CubicDual

open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex.Supplement

/-- Nesterov–Polyak 2006, Theorem 10, (5.2)–(5.3), p. 198. For any vector `g`, any symmetric
operator `H` and any `M > 0`:
* (5.2) the primal cubic function `v_u` attains its minimum over `ℝⁿ`, and its minimal value is
  the supremum (least upper bound, not necessarily attained) of `v_l` over the dual domain `𝒟`;
* (5.3) for every `r ∈ 𝒟`, with `h(r) = −(H + (Mr/2) I)⁻¹ g`,
  `0 ≤ v_u(h(r)) − v_l(r) = (M/12)(r + 2‖h(r)‖)(‖h(r)‖ − r)²
     = (4/(3M)) · ((r + 2‖h(r)‖)/(r + ‖h(r)‖)²) · v_l′(r)²`,
  where `v_l′` is the derivative of `v_l`. -/
theorem theorem_10 {n : ℕ} (g : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ a b : EuclideanSpace ℝ (Fin n), ⟪H a, b⟫ = ⟪a, H b⟫)
    (M : ℝ) (hM : 0 < M) :
    (∃ hs : EuclideanSpace ℝ (Fin n), (∀ h, vu g H M hs ≤ vu g H M h) ∧
        IsLUB (vl g H M '' dualDomain H M) (vu g H M hs)) ∧
      ∀ r ∈ dualDomain H M,
        0 ≤ vu g H M (hDir g H M r) - vl g H M r ∧
        vu g H M (hDir g H M r) - vl g H M r =
          M / 12 * (r + 2 * ‖hDir g H M r‖) * (‖hDir g H M r‖ - r) ^ 2 ∧
        vu g H M (hDir g H M r) - vl g H M r =
          4 / (3 * M) * ((r + 2 * ‖hDir g H M r‖) / (r + ‖hDir g H M r‖) ^ 2) *
            deriv (vl g H M) r ^ 2 := by sorry

end CubicNewton.Nonconvex.Supplement
