-- Prove2me | Theorems.Thm_AugLagLLC_KKT_cpld_limit_kkt
-- name    : AugLagLLC.KKT.cpld_limit_kkt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:36:58.604979+00:00
-- url     : https://prove2.me/theorems/b6616e94-53fd-4d8d-88b2-1f8ed180eb7d
-- title:
--   (4.11)–(4.15), proof of Theorem 4.2, pp. 9–10 — approximate KKT sequences converge to KKT points under CPLD
-- statement:
--   Consider the nonlinear program "minimize $F(x)$ subject to $H_i(x)=0$ ($i\in\iota$), $G_j(x)\le 0$ ($j\in\kappa$)" on $\mathbb R^n$ with finite index sets and continuously differentiable $F$, $H_i$, $G_j$. Let $x_*$ be feasible and satisfy the CPLD condition, and let $y_k\to x_*$. Suppose there are coefficients $a_k\in\mathbb R^\iota$ and $b_k\in\mathbb R^\kappa$ such that, for every $k$,
--
--   1. $[b_k]_j\ge 0$ for all $j$, and $[b_k]_j=0$ whenever $G_j(x_*)<0$;
--   2. the residual tends to zero:
--   $$\nabla F(y_k)+\sum_{i\in\iota}[a_k]_i\nabla H_i(y_k)+\sum_{j\in\kappa}[b_k]_j\nabla G_j(y_k)\ \longrightarrow\ 0\qquad(k\to\infty).$$
--
--   Then $x_*$ is a KKT point of the program.
--
--   This is the core of Theorem 4.2 with the algorithm abstracted away: by (4.9) and (4.10), the iterates of Algorithm 3.1 along a subsequence converging to $x_*$ satisfy (4.11), which is exactly the hypothesis above with $F=f$, the equality constraints $h_1,h_2$, the inequality constraints $g_1,g_2$, and $a_k=(\lambda_{k+1},v_k)$, $b_k=(\mu_{k+1},u_k)$.
--
--   **Formalization Note.** The paper's index sets "$k\in K$, $k\ge k_5$" are re-indexed as the whole sequence $k\in\mathbb N$. The sign and support conditions on $b_k$ refer to the constraints inactive at the limit $x_*$, as in (4.11), not at $y_k$. CPLD and KKT are the definitions of `AugLagLLC.KKT.ConstraintQualifications`.
-- source:
--   Andreani, Birgin, Martínez & Schuverdt, On augmented Lagrangian methods with general lower-level constraints, HAL hal-01295437v1, pp. 9–10, proof of Theorem 4.2, (4.11)–(4.15)

import Mathlib
import Definitions.Def_AugLagLLC_KKT_ConstraintQualifications

namespace AugLagLLC.KKT

open Filter Topology

/-- (4.11)–(4.15), proof of Theorem 4.2, pp. 9–10, without the algorithm: let `F`, `H i`, `G j`
be `C¹`, let `xs` be feasible and satisfy CPLD, and let `yₖ → xs`. If there are coefficients
`aₖ` (free) and `bₖ ≥ 0`, with `[bₖ]ⱼ = 0` for every constraint inactive at `xs`, such that
`∇F(yₖ) + ∑ᵢ [aₖ]ᵢ ∇Hᵢ(yₖ) + ∑ⱼ [bₖ]ⱼ ∇Gⱼ(yₖ) → 0`, then `xs` is a KKT point. -/
theorem cpld_limit_kkt {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {H : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {G : κ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : ContDiff ℝ 1 F) (hH : ∀ i, ContDiff ℝ 1 (H i)) (hG : ∀ j, ContDiff ℝ 1 (G j))
    {xs : EuclideanSpace ℝ (Fin n)} (hHx : ∀ i, H i xs = 0) (hGx : ∀ j, G j xs ≤ 0)
    (hcpld : CPLDAt H G xs)
    {y : ℕ → EuclideanSpace ℝ (Fin n)} (hy : Tendsto y atTop (𝓝 xs))
    (a : ℕ → ι → ℝ) (b : ℕ → κ → ℝ) (hb : ∀ k j, 0 ≤ b k j)
    (hbG : ∀ k j, G j xs < 0 → b k j = 0)
    (hres : Tendsto (fun k => gradient F (y k) + ∑ i, a k i • gradient (H i) (y k)
        + ∑ j, b k j • gradient (G j) (y k)) atTop (𝓝 0)) :
    IsKKT F H G xs := by sorry

end AugLagLLC.KKT
