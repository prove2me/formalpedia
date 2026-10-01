-- Prove2me | Theorems.Thm_FirstOrderOpt_ProjectionFree_saddle_point_cndg_rate
-- name    : FirstOrderOpt.ProjectionFree.saddle_point_cndg_rate
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:04:56.816368+00:00
-- url     : https://prove2.me/theorems/2a38f50b-5af2-408e-ab6d-d41c1c0228ce
-- title:
--   Theorem 7.2 — modified conditional gradient method for bilinear saddle-point problems
-- statement:
--   Continuing `smoothed_objective_monotone` (Lemma 7.1)'s setting: $f(x) := \max_{y\in Y}
--   \{\langle Ax,y\rangle-\hat f(y)\}$ (Eq. (7.1.5)), $X$ compact convex. The modified CndG method
--   runs Algorithm 7.1 with $f'(y_{k-1})$ replaced by $f_{\eta_k}'(y_{k-1})$, the gradient of the
--   smoothed objective at parameter $\eta_k$ (which is differentiable with Lipschitz gradient by
--   Lemma 3.7 — not restated here), for a nonincreasing sequence $\eta_1\ge\eta_2\ge\dots>0$ (Eq.
--   (7.1.26)), with $\|A\|$ the operator norm and $\sigma_v$ the strong-convexity modulus of
--   $\omega$ from (7.1.21).
--
--   **Theorem 7.2.** For stepsizes $\alpha_k$ set to (7.1.9) or (7.1.10), and for every
--   $k=1,2,\dots$,
--   $$f(y_k) - f^* \le \frac{2}{k(k+1)}\sum_{i=1}^k\Big[i\,\eta_i D_Y^2 +
--   \frac{\|A\|^2}{\sigma_v\eta_i}\|x_i-y_{i-1}\|^2\Big].$$
--
--   This is the saddle-point counterpart of the goal theorem (`conditional_gradient_rate`, Theorem
--   7.1): the same telescoping argument, applied to the smoothed objectives $f_{\eta_k}$ instead of
--   $f$ directly, using Lemma 7.1's monotonicity to compare $f_{\eta_{k-1}}(y_{k-1})$ against
--   $f_{\eta_k}(y_{k-1})$ across the telescoping sum, plus (7.1.24)'s sandwich $f(x)\le
--   f_\eta(x)\le f(x)+\eta D_Y^2$ to relate the smoothed bound back to $f$ itself.
--
--   **Formalization Note.** As in `conditional_gradient_rate`, `hyk_le` packages both stepsize
--   policies (7.1.9)/(7.1.10) as a single hypothesis: under either, $f_{\eta_k}(y_k) \le
--   f_{\eta_k}(\tilde y_k)$ for the fixed-schedule comparison point $\tilde y_k$ built with
--   $\gamma_k=2/(k+1)$. $f_{\eta_k}'$ is left as a free gradient selector `fηGrad`, since its
--   specific relationship to $f_\eta$ (via Lemma 3.7's Lipschitz-gradient property, from an
--   earlier chapter) is not itself part of this milestone's statement — matching how
--   `conditional_gradient_rate` leaves the general-smoothness gradient `fGrad` free of any
--   definitional tie to `f` beyond the Lipschitz bound it needs.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 427, Theorem 7.2

import Mathlib

namespace FirstOrderOpt.ProjectionFree

open scoped RealInnerProductSpace

/-- Theorem 7.2 — the modified CndG method for bilinear saddle-point problems. `f(x) :=
max_{y∈Y}{⟨Ax,y⟩-f̂(y)}` (Eq. (7.1.5)); the algorithm is Algorithm 7.1 with `f'(y(k-1))` replaced
by `fη k`'s gradient selector `fηGrad k` at `y (k-1)`, for a nonincreasing sequence `η k > 0`
(Eq. (7.1.26)). `hyk_le` is the saddle-point analogue of `conditional_gradient_rate`'s `hyk_le`:
under either stepsize policy (7.1.9)/(7.1.10), `fη k (y k) ≤ fη k (ỹ k)` for the fixed-schedule
comparison point `ỹ k`. Then, for every `k ≥ 1`,
`f(y k) - f* ≤ (2/(k(k+1))) Σ_{i=1}^k [i·η(i)·D_Y² + (‖A‖²/(σv·η(i)))‖x i - y(i-1)‖²]`
(Eq. (7.1.27)).

**Formalization Note (revised 2026-09-19).** `hYconv`/`hYcompact` state (7.1.5)'s standing
assumption on `Y`, previously absent. `hfbdd` guards `hf`'s `sSup` (same convention as
`smoothed_objective_monotone`'s `hbdd`). `hsandwich` states the sandwich (7.1.24) between `f` and
`fη k` that the proof and this item's own prose already relied on but did not hypothesize.
`hηSmooth` states the Lipschitz-gradient rate (7.1.25) for `fηGrad k` at the book's own constant
`Lη_k = ‖A‖²/(σv·η_k)`. `hcvx` is the saddle-point analogue of `conditional_gradient_rate`'s
`hcvx`, the convexity of `fη k` used the same way in the proof. -/
theorem saddle_point_cndg_rate {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (X : Set E) (hXconv : Convex ℝ X) (hXcompact : IsCompact X)
    (Y : Set F) (hYconv : Convex ℝ Y) (hYcompact : IsCompact Y)
    (A : E →L[ℝ] F) (fhat : F → ℝ)
    (f : E → ℝ) (hf : ∀ x, f x = sSup ((fun y => ⟪A x, y⟫ - fhat y) '' Y))
    (hfbdd : ∀ x, BddAbove ((fun y => ⟪A x, y⟫ - fhat y) '' Y))
    (σv DY : ℝ) (hσv : 0 < σv) (hDY : 0 < DY)
    (η : ℕ → ℝ) (hηpos : ∀ k, 1 ≤ k → 0 < η k) (hηmono : ∀ k, 1 ≤ k → η (k + 1) ≤ η k)
    (fη : ℕ → E → ℝ) (fηGrad : ℕ → E → E →L[ℝ] ℝ)
    (hsandwich : ∀ k, 1 ≤ k → ∀ z ∈ X, f z ≤ fη k z ∧ fη k z ≤ f z + η k * DY ^ 2)
    (hηSmooth : ∀ k, 1 ≤ k → ∀ a ∈ X, ∀ b ∈ X,
      ‖fηGrad k a - fηGrad k b‖ ≤ (‖A‖ ^ 2 / (σv * η k)) * ‖a - b‖)
    (hcvx : ∀ k, 1 ≤ k → ∀ a ∈ X, ∀ b ∈ X, fη k a + (fηGrad k a) (b - a) ≤ fη k b)
    (x y : ℕ → E) (hx0 : x 0 ∈ X) (hy0 : y 0 = x 0)
    (hx : ∀ k, 1 ≤ k → x k ∈ X) (hy : ∀ k, y k ∈ X)
    (hLO : ∀ k, 1 ≤ k → ∀ z ∈ X, (fηGrad k (y (k - 1))) (x k) ≤ (fηGrad k (y (k - 1))) z)
    (α : ℕ → ℝ) (hα : ∀ k, 1 ≤ k → α k ∈ Set.Icc (0 : ℝ) 1)
    (hyDef : ∀ k, 1 ≤ k → y k = (1 - α k) • y (k - 1) + (α k) • x k)
    (hyk_le : ∀ k, 1 ≤ k →
      fη k (y k) ≤ fη k ((1 - 2 / ((k : ℝ) + 1)) • y (k - 1) + (2 / ((k : ℝ) + 1)) • x k))
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ z ∈ X, f xstar ≤ f z)
    (k : ℕ) (hk : 1 ≤ k) :
    f (y k) - f xstar ≤ (2 / ((k : ℝ) * ((k : ℝ) + 1))) *
      ∑ i ∈ Finset.Icc 1 k, ((i : ℝ) * η i * DY ^ 2 +
        (‖A‖ ^ 2 / (σv * η i)) * ‖x i - y (i - 1)‖ ^ 2) := by sorry

end FirstOrderOpt.ProjectionFree
