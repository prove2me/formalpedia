-- Prove2me | Theorems.Thm_AugLagLLC_KKT_mfcq_multipliers_bounded
-- name    : AugLagLLC.KKT.mfcq_multipliers_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:37:14.797676+00:00
-- url     : https://prove2.me/theorems/1879af2b-90db-408e-a274-6005665683a7
-- title:
--   (4.8) under MFCQ, proof of Theorem 4.2, p. 10 — the multipliers of an approximate KKT sequence are bounded
-- statement:
--   Consider the nonlinear program "minimize $F(x)$ subject to $H_i(x)=0$ ($i\in\iota$), $G_j(x)\le 0$ ($j\in\kappa$)" on $\mathbb R^n$ with finite index sets and continuously differentiable $F$, $H_i$, $G_j$. Let $x_*$ be feasible and satisfy MFCQ, and let $y_k\to x_*$. Suppose there are coefficients $a_k\in\mathbb R^\iota$ and $b_k\in\mathbb R^\kappa$ with $[b_k]_j\ge 0$ for all $j$, $[b_k]_j=0$ whenever $G_j(x_*)<0$, and
--   $$\nabla F(y_k)+\sum_{i\in\iota}[a_k]_i\nabla H_i(y_k)+\sum_{j\in\kappa}[b_k]_j\nabla G_j(y_k)\ \longrightarrow\ 0 .$$
--   Then the sequences $\{a_k\}$ and $\{b_k\}$ are bounded: there is $C$ with
--   $$\|a_k\|_\infty\le C\quad\text{and}\quad\|b_k\|_\infty\le C\qquad\text{for all }k .$$
--
--   Applied to (4.11) along a subsequence of Algorithm 3.1 converging to $x_*$, this gives the boundedness (4.8) of the multiplier estimates $\lambda_{k+1}$, $\mu_{k+1}$, $v_k$, $u_k$.
--
--   **Formalization Note.** The norms are the sup norms on `ι → ℝ` and `κ → ℝ`, matching the $B_k$ of the page. Boundedness for all $k$ is equivalent to boundedness from some index on, since finitely many terms are bounded.
-- source:
--   Andreani, Birgin, Martínez & Schuverdt, On augmented Lagrangian methods with general lower-level constraints, HAL hal-01295437v1, p. 10, proof of Theorem 4.2, (4.8) under MFCQ

import Mathlib
import Definitions.Def_AugLagLLC_KKT_ConstraintQualifications

namespace AugLagLLC.KKT

open Filter Topology

/-- (4.8) under MFCQ, proof of Theorem 4.2, p. 10, without the algorithm: in the setting of
`cpld_limit_kkt` with MFCQ at `xs` in place of CPLD, the coefficient sequences `aₖ`, `bₖ` are
bounded (in the sup norm). -/
theorem mfcq_multipliers_bounded {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {H : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {G : κ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : ContDiff ℝ 1 F) (hH : ∀ i, ContDiff ℝ 1 (H i)) (hG : ∀ j, ContDiff ℝ 1 (G j))
    {xs : EuclideanSpace ℝ (Fin n)} (hHx : ∀ i, H i xs = 0) (hGx : ∀ j, G j xs ≤ 0)
    (hmfcq : MFCQAt H G xs)
    {y : ℕ → EuclideanSpace ℝ (Fin n)} (hy : Tendsto y atTop (𝓝 xs))
    (a : ℕ → ι → ℝ) (b : ℕ → κ → ℝ) (hb : ∀ k j, 0 ≤ b k j)
    (hbG : ∀ k j, G j xs < 0 → b k j = 0)
    (hres : Tendsto (fun k => gradient F (y k) + ∑ i, a k i • gradient (H i) (y k)
        + ∑ j, b k j • gradient (G j) (y k)) atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ k, ‖a k‖ ≤ C ∧ ‖b k‖ ≤ C := by sorry

end AugLagLLC.KKT
