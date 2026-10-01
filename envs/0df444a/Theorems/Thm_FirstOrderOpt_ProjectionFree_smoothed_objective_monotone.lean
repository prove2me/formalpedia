-- Prove2me | Theorems.Thm_FirstOrderOpt_ProjectionFree_smoothed_objective_monotone
-- name    : FirstOrderOpt.ProjectionFree.smoothed_objective_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:04:35.079818+00:00
-- url     : https://prove2.me/theorems/d8cc9c6e-3d6f-4fa1-80d4-df48ca459cd1
-- title:
--   Lemma 7.1 — monotonicity of the smoothed saddle-point objective
-- statement:
--   For a bilinear saddle-point objective $f(x)=\max_{y\in Y}\{\langle Ax,y\rangle-\hat f(y)\}$
--   (Eq. (7.1.5)), where $Y\subseteq\mathbb R^m$ is convex compact, $A$ a linear operator, and
--   $\hat f$ convex, a smoothing family is built from a strongly convex $\omega:Y\to\mathbb R$
--   (Eq. (7.1.21)) via its Bregman-type divergence $V$ (called $W$ at its first appearance, Eq.
--   (7.1.22)) and diameter $D_Y := [\max_{y\in Y}V(y)]^{1/2}$, so that $0\le V(y)\le D_Y^2$ for
--   all $y\in Y$:
--   $$f_\eta(x) := \max_{y\in Y}\Big\{\langle Ax,y\rangle - \hat f(y) - \eta\big[V(y)-D_Y^2\big]
--   \Big\}, \qquad \eta \ge 0. \quad (7.1.23)$$
--
--   **Lemma 7.1.** Let $\eta_1\ge\eta_2\ge0$. Then $f_{\eta_1}(x)\ge f_{\eta_2}(x)$ for every
--   $x\in X$.
--
--   This is the one-line observation that licenses the modified CndG method's variable smoothing
--   parameter $\eta_k$: since $V(y)-D_Y^2\le0$, increasing $\eta$ only ever *raises* the value
--   subtracted... equivalently raises $-\eta[V(y)-D_Y^2]\ge0$, pointwise in $y$, hence raises the
--   max over $y\in Y$. `saddle_point_cndg_rate` (Theorem 7.2) below uses this monotonicity, via
--   (7.1.26)'s nonincreasing schedule $\eta_1\ge\eta_2\ge\dots$, to compare consecutive smoothed
--   objectives $f_{\eta_{k-1}}$ and $f_{\eta_k}$ in its own telescoping argument.
--
--   **Formalization Note.** $f_\eta$ is realized as `sSup` of the image of $Y$ under the pointwise
--   objective, matching the book's `max_{y∈Y}{...}` exactly (a genuine maximum exists because $Y$
--   is compact and the objective continuous, though existence itself is not part of this lemma's
--   statement — no `IsCompact Y` hypothesis is needed for the inequality `sSup S1 ≤ sSup S2`
--   itself, only for `sSup` to coincide with an attained maximum, which is not asserted here).
--   $\langle\cdot,\cdot\rangle$ is Mathlib's real inner product on the codomain of $A$.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 426, Lemma 7.1

import Mathlib

namespace FirstOrderOpt.ProjectionFree

open scoped RealInnerProductSpace

/-- Lemma 7.1 (monotonicity of the smoothing family). `fη(x) := max_{y∈Y}{⟨Ax,y⟩ - f̂(y) -
η[V(y)-D_Y²] : y∈Y}` (Eq. (7.1.23)), realized here as `sSup` of the image of `Y` under the
objective; `V` is the Bregman-type divergence of (7.1.21)-(7.1.22), bounded above by `D_Y²`
(`hVbound`, from `0 ≤ V(y) ≤ D_Y²`). If `η1 ≥ η2 ≥ 0`, then `fη1(x) ≥ fη2(x)` for every `x`: since
`V(y) - D_Y² ≤ 0`, the term `-η[V(y)-D_Y²]` is pointwise nondecreasing in `η ≥ 0`, hence so is the
`sSup`. `hbdd` requires the image set to be bounded above at the larger parameter `η1` (for every
`x`), since Mathlib's `sSup` of an unbounded-above set of reals is `0` by convention, which would
otherwise let an unbounded objective family satisfy the stated monotonicity vacuously regardless
of its true supremum. -/
theorem smoothed_objective_monotone {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (Y : Set F) (A : E →L[ℝ] F) (fhat V : F → ℝ) (DY : ℝ)
    (hVbound : ∀ y ∈ Y, V y ≤ DY ^ 2)
    (fη : ℝ → E → ℝ)
    (hfη : ∀ η x, fη η x = sSup ((fun y => ⟪A x, y⟫ - fhat y - η * (V y - DY ^ 2)) '' Y))
    (η1 η2 : ℝ) (hη : η2 ≤ η1) (hη2 : 0 ≤ η2) (x : E)
    (hbdd : ∀ η, 0 ≤ η → BddAbove ((fun y => ⟪A x, y⟫ - fhat y - η * (V y - DY ^ 2)) '' Y)) :
    fη η2 x ≤ fη η1 x := by sorry

end FirstOrderOpt.ProjectionFree
