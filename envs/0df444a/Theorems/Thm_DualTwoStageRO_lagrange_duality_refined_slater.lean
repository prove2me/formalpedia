-- Prove2me | Theorems.Thm_DualTwoStageRO_lagrange_duality_refined_slater
-- name    : DualTwoStageRO.lagrange_duality_refined_slater
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:47:57.057122+00:00
-- url     : https://prove2.me/theorems/b2b96e15-f203-44c0-b371-fdea5bf6158d
-- title:
--   Lagrangian strong duality under a refined Slater point (first dualization, Assumption 1)
-- statement:
--   Let $\varphi,h_1,\dots,h_m:\mathbb R^n\to\mathbb R$ be convex, $E\in\mathbb R^{r\times n}$ and $e\in\mathbb R^r$. Suppose some $\bar y$ satisfies $h_i(\bar y)\le0$ for all $i$, $h_i(\bar y)<0$ for every $i$ for which $h_i$ is not affine, and $E\bar y=e$. Then there is no duality gap:
--
--   $$\inf\bigl\{\varphi(y):\ h_i(y)\le0\ (i=1,\dots,m),\ Ey=e\bigr\}=\sup_{\mu\ge0}\ \sup_{w\in\mathbb R^r}\ \inf_{y\in\mathbb R^n}\Bigl\{\varphi(y)+\sum_{i=1}^m\mu_ih_i(y)+w^\top(Ey-e)\Bigr\},$$
--
--   in the extended reals, including the case in which both sides are $-\infty$.
--
--   This is the first of the two dualizations behind Theorem 1: Assumption 1 provides exactly such a point for the inner problem of (1), strictly feasible only for the constraints with a nonlinear $g_i$.
--
--   **Formalization Note** Values in `EReal`; no boundedness below and no attainment is assumed.
--
--   Differences from the source:
--   - generalization: Assumption 1's point for the inner problem of (1) at (x, ζ), used to dualize over y → an arbitrary convex program with finite convex φ, h_i on ℝⁿ and affine equalities Ey = e; reason: the inner problem of (1) is the instance φ = f0(x) + g0, h_i = ζ⊤F_i·(x) + f_i(x) + g_i, E = B, e = b(x) − A(x)ζ
--   - reading: strict inequality for all i = 1,…,m1 for which g_i is nonlinear → strict inequality for every i with g_i not affine (IsAffineFun); reason: an affine g_i is "linear" in the optimization sense; this is the weaker hypothesis, so the stronger theorem
--   - encoding: optimal values possibly ±∞ → EReal; reason: Lean convention; same instances
-- source:
--   de Ruiter, Zhen, den Hertog, Technical Note—Dual Approach for Two-Stage Robust Nonlinear Optimization, Operations Research 71(5):1794–1799, 2023, doi:10.1287/opre.2022.2289 (published version, sha256 75cbce38…fe03ac), Assumption 1, p.1795, and the remark after it, p.1796; abstract, p.1794 ("first dualizing over the adjustable variables")

import Mathlib
import Definitions.Def_DualTwoStageRO_IsAffineFun

namespace DualTwoStageRO

open Matrix

/-- **Lagrangian strong duality under a refined Slater point** (the first dualization, over the
adjustable variables). de Ruiter, Zhen, den Hertog, Operations Research 71(5), 2023: the
reformulation is "obtained by first dualizing over the adjustable variables" (abstract, p.1794);
Assumption 1 (p.1795) supplies a point that is feasible and strictly feasible for "all nonlinear
constraints that contain the wait and see decision variables" (p.1796).

Let `φ` and `h_1,…,h_m` be convex real-valued functions on `ℝⁿ`, `E ∈ ℝ^{r×n}`, `e ∈ ℝ^r`, and let
`ȳ` satisfy `h_i(ȳ) ≤ 0` for all `i`, `h_i(ȳ) < 0` for every `h_i` that is not affine, and `Eȳ = e`.
Then
`inf {φ(y) | h_i(y) ≤ 0 ∀ i, Ey = e} = sup_{μ ≥ 0} sup_w inf_y [φ(y) + Σ_i μ_i h_i(y) + w⊤(Ey − e)]`
in `EReal`, including the case where both sides are `−∞`.

**Formalization Note.** No boundedness below and no attainment is assumed. -/
theorem lagrange_duality_refined_slater {n m r : ℕ} (φ : (Fin n → ℝ) → ℝ)
    (h : Fin m → (Fin n → ℝ) → ℝ) (E : Matrix (Fin r) (Fin n) ℝ) (e : Fin r → ℝ)
    (hφ : ConvexOn ℝ Set.univ φ) (hh : ∀ i, ConvexOn ℝ Set.univ (h i))
    (ybar : Fin n → ℝ) (hfeas : ∀ i, h i ybar ≤ 0)
    (hstrict : ∀ i, ¬ IsAffineFun (h i) → h i ybar < 0) (hE : E *ᵥ ybar = e) :
    (⨅ y ∈ {y : Fin n → ℝ | (∀ i, h i y ≤ 0) ∧ E *ᵥ y = e}, (φ y : EReal)) =
      ⨆ μ ∈ {μ : Fin m → ℝ | 0 ≤ μ}, ⨆ w : Fin r → ℝ, ⨅ y : Fin n → ℝ,
        ((φ y + ∑ i, μ i * h i y + w ⬝ᵥ (E *ᵥ y - e) : ℝ) : EReal) := by sorry

end DualTwoStageRO
