-- Prove2me | Theorems.Thm_ConicBlackwell_Supplement_theorem_2_1
-- name    : ConicBlackwell.Supplement.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:47:05.279479+00:00
-- url     : https://prove2.me/theorems/d7b6f6f1-e041-4f53-93ae-10a78be89392
-- title:
--   Theorem 2.1 — the duality gap of the averaged decisions is at most $(R_{T,x}+R_{T,y})/T$
-- statement:
--   Let $\mathcal X\subset\mathbb R^n$ and $\mathcal Y\subset\mathbb R^m$ be nonempty convex compact sets and $F:\mathcal X\times\mathcal Y\to\mathbb R$ convex in $x$ and concave in $y$. Let $T\ge1$ and let $x_1,\dots,x_T\in\mathcal X$, $y_1,\dots,y_T\in\mathcal Y$ be any decisions, with losses $f_t\in\partial_xF(x_t,y_t)$ (a subgradient of $F(\cdot,y_t)$ at $x_t$) and $g_t\in\partial_yF(x_t,y_t)$ (a supergradient of $F(x_t,\cdot)$ at $y_t$). Define the regrets
--
--   $$
--   R_{T,x}=\sum_{t=1}^T\langle f_t,x_t\rangle-\min_{x\in\mathcal X}\sum_{t=1}^T\langle f_t,x\rangle,\qquad R_{T,y}=\max_{y\in\mathcal Y}\sum_{t=1}^T\langle g_t,y\rangle-\sum_{t=1}^T\langle g_t,y_t\rangle,
--   $$
--
--   and the averages $(\bar x_T,\bar y_T)=\frac1T\sum_{t=1}^T(x_t,y_t)$. Then
--
--   $$
--   \max_{y\in\mathcal Y}F(\bar x_T,y)-\min_{x\in\mathcal X}F(x,\bar y_T)\ \le\ \frac{R_{T,x}+R_{T,y}}{T}.
--   $$
--
--   This is what makes the repeated game framework a solver for the saddle-point problem $\min_{x\in\mathcal X}\max_{y\in\mathcal Y}F(x,y)$: if both players use regret minimizers with regret $O(\sqrt T)$, the averaged decisions have duality gap $O(1/\sqrt T)$.
--
--   **Formalization Note** $\mathbb R^n$ is `E n`. $F$ is a function on $\mathbb R^n\times\mathbb R^m$ whose values off $\mathcal X\times\mathcal Y$ are never read. The subgradient is the published `BubeckCO.PSGD.IsSubgradient`, relative to $\mathcal X$ (it includes $x_t\in\mathcal X$); the supergradient $g_t$ is written as a subgradient $-g_t$ of $-F(x_t,\cdot)$ relative to $\mathcal Y$. The max and min of $F$ are the supremum and infimum of images; under the hypotheses both sets are bounded, so these are the true sup and inf (attained when $F$ is continuous). $R_{T,x}$ is `weightedRegret X 1 f x T`.
--
--   Differences from the source:
--   - generalization: F subdifferentiable on X × Y (problem (1), p.1) → only the (super)gradients f_t, g_t at the played points (x_t, y_t) are assumed to exist; reason: the theorem uses no other subgradient; every subdifferentiable F supplies them, so the statement specializes to the source's
--   - encoding: max_{y∈Y} F(x̄_T, y) and min_{x∈X} F(x, ȳ_T) → sSup and sInf of the images of Y and X; reason: both sets are nonempty and bounded under the hypotheses (by the supergradient and subgradient inequalities at the played points), so sSup/sInf are their sup/inf, and equal the max/min whenever these are attained
--   - encoding: ∂_xF(x_t, y_t), ∂_yF(x_t, y_t) → IsSubgradient X (F(·, y_t)) x_t f_t and IsSubgradient Y (−F(x_t, ·)) y_t (−g_t); reason: subgradients of a function on X × Y are relative to X and Y; the second is the supergradient inequality F(x_t, y') ≤ F(x_t, y_t) + ⟨g_t, y' − y_t⟩ for y' ∈ Y
--   - encoding: min_{x∈X} Σ⟨f_t, x⟩ and max_{y∈Y} Σ⟨g_t, y⟩ → sInf and sSup of the images (weightedRegret X 1 f x T for R_{T,x}); reason: a linear function on a nonempty compact set attains both
--   - encoding: ℝⁿ, ℝᵐ and rounds t = 1, …, T → E n, E m and sequences ℕ → · read on Finset.Icc 1 T; reason: Lean convention; same instances
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), Theorem 2.1, p.4 (regrets R_{T,x}, R_{T,y}, p.4; problem (1), p.1)

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_Cones
import Definitions.Def_BubeckCO_PSGD_IsSubgradient
import Definitions.Def_ConicBlackwell_weightedRegret
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell.Supplement

/-- **Theorem 2.1**, Grand-Clément & Kroer, arXiv:2202.12277v1, p.4.
Let `X ⊂ ℝⁿ`, `Y ⊂ ℝᵐ` be convex compact sets and `F : X × Y → ℝ` convex-concave.  For any
decisions `x_t ∈ X`, `y_t ∈ Y` (`1 ≤ t ≤ T`) with `f_t ∈ ∂_xF(x_t, y_t)` and `g_t ∈ ∂_yF(x_t, y_t)`,
the uniform averages `(x̄_T, ȳ_T) = (1/T) Σ_{t=1}^T (x_t, y_t)` satisfy
`max_{y∈Y} F(x̄_T, y) − min_{x∈X} F(x, ȳ_T) ≤ (R_{T,x} + R_{T,y})/T`, where
`R_{T,x} = Σ_t ⟨f_t, x_t⟩ − min_{x∈X} Σ_t ⟨f_t, x⟩` and
`R_{T,y} = max_{y∈Y} Σ_t ⟨g_t, y⟩ − Σ_t ⟨g_t, y_t⟩` (p.4).

Formalization Note: `ℝⁿ = E n`; `F` is a function on `E n × E m` whose values off `X × Y` are
never read; convex-concave is `ConvexOn ℝ X (F · y)` for `y ∈ Y` and `ConcaveOn ℝ Y (F x ·)` for
`x ∈ X`.  `f_t ∈ ∂_xF(x_t, y_t)` is the published `BubeckCO.PSGD.IsSubgradient` relative to `X`
(it includes `x_t ∈ X`); `g_t ∈ ∂_yF(x_t, y_t)` (a supergradient of the concave `F(x_t, ·)`) is
`IsSubgradient Y (−F(x_t, ·)) y_t (−g_t)`, i.e. `y_t ∈ Y` and
`F(x_t, y') ≤ F(x_t, y_t) + ⟨g_t, y' − y_t⟩` for `y' ∈ Y`.  Only the (super)gradients at the played
points are assumed, not subdifferentiability everywhere.  The max and min of `F` are `sSup`/`sInf`
of images (both sets are bounded under these hypotheses, so these are the true sup and inf);
`R_{T,x}` is `weightedRegret X 1 f x T`, and the max in `R_{T,y}` is `sSup` of the image of `Y`
(attained: a linear function on a nonempty compact set). -/
theorem theorem_2_1 {n m : ℕ} (X : Set (E n)) (Y : Set (E m))
    (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (hYne : Y.Nonempty) (hYc : IsCompact Y) (hYcv : Convex ℝ Y)
    (F : E n → E m → ℝ)
    (hFx : ∀ y' ∈ Y, ConvexOn ℝ X (fun x' => F x' y'))
    (hFy : ∀ x' ∈ X, ConcaveOn ℝ Y (fun y' => F x' y'))
    (x : ℕ → E n) (y : ℕ → E m) (f : ℕ → E n) (g : ℕ → E m) (T : ℕ) (hT : 1 ≤ T)
    (hf : ∀ t ∈ Finset.Icc 1 T,
      BubeckCO.PSGD.IsSubgradient X (fun x' => F x' (y t)) (x t) (f t))
    (hg : ∀ t ∈ Finset.Icc 1 T,
      BubeckCO.PSGD.IsSubgradient Y (fun y' => -F (x t) y') (y t) (-g t)) :
    sSup ((fun y' => F ((T : ℝ)⁻¹ • ∑ t ∈ Finset.Icc 1 T, x t) y') '' Y)
        - sInf ((fun x' => F x' ((T : ℝ)⁻¹ • ∑ t ∈ Finset.Icc 1 T, y t)) '' X) ≤
      (weightedRegret X (fun _ => 1) f x T
        + (sSup ((fun y' => ∑ t ∈ Finset.Icc 1 T, ⟪g t, y'⟫) '' Y)
            - ∑ t ∈ Finset.Icc 1 T, ⟪g t, y t⟫)) / T := by sorry

end ConicBlackwell.Supplement
