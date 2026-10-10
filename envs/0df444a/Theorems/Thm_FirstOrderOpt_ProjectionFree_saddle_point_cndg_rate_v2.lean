-- Prove2me | Theorems.Thm_FirstOrderOpt_ProjectionFree_saddle_point_cndg_rate_v2
-- name    : FirstOrderOpt.ProjectionFree.saddle_point_cndg_rate_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:17:19.562187+00:00
-- url     : https://prove2.me/theorems/dbffd99e-096e-427c-937e-9b35774db076
-- title:
--   Theorem 7.2 — conditional gradient for bilinear saddle-point problems (corrected: smoothing defined)
-- statement:
--   Let $X\subseteq E$ be compact convex, $Y\subseteq F$ compact convex nonempty ($F$ an inner-product space), $A:E\to F$ linear, $\hat f$ convex and lower semicontinuous on $Y$, and $f(x)=\max_{y\in Y}\{\langle Ax,y\rangle-\hat f(y)\}$ (7.1.5). Let $\omega$ be a distance generating function on $Y$ with modulus $\sigma_v$ (differentiable along $Y$ and $\sigma_v$-strongly convex), $c=\arg\min_Y\omega$, $V_Y(y)=\omega(y)-\omega(c)-\langle\omega'(c),y-c\rangle$ and $D_Y^2=\max_{y\in Y}V_Y(y)$. For a nonincreasing sequence $\eta_k>0$ define the smooth approximations $f_{\eta_k}(x)=\max_{y\in Y}\{\langle Ax,y\rangle-\hat f(y)-\eta_kV_Y(y)\}$ (7.1.22), with gradients $\nabla f_{\eta_k}$. Run Algorithm 7.1 with $f'(y_{k-1})$ replaced by $\nabla f_{\eta_k}(y_{k-1})$ (7.1.26): $x_k\in\arg\min_{z\in X}\langle\nabla f_{\eta_k}(y_{k-1}),z\rangle$ and $y_k=(1-\alpha_k)y_{k-1}+\alpha_kx_k$ under either stepsize policy (7.1.9) or (7.1.10) (both guarantee $f_{\eta_k}(y_k)\le f_{\eta_k}(\tilde y_k)$ for the fixed-schedule point $\tilde y_k=(1-\tfrac2{k+1})y_{k-1}+\tfrac2{k+1}x_k$). Then for every $k\ge 1$, (7.1.27):
--   $$f(y_k)-f^*\le\frac2{k(k+1)}\sum_{i=1}^k\Big[i\,\eta_iD_Y^2+\frac{\|A\|^2}{\sigma_v\eta_i}\|x_i-y_{i-1}\|^2\Big].$$
--
--   **Formalization Note.** The retired statement took each $f_{\eta_k}$ as a free function constrained only by a sandwich, a smoothness bound and a convexity inequality, so nothing related $f_{\eta_k}$ to $f_{\eta_{k-1}}$ and the monotonicity of Lemma 7.1 was unavailable (disproved). The corrected statement defines $f_{\eta_k}$ from the data as the Nesterov smoothing (7.1.22) with the prox-function of a distance generating function on $Y$, so the sandwich $f_\eta\le f\le f_\eta+\eta D_Y^2$, the monotonicity in $\eta$ and the Lipschitz-gradient bound $\|A\|^2/(\sigma_v\eta)$ are consequences; $\nabla f_{\eta_k}$ is tied to $f_{\eta_k}$ by `HasFDerivWithinAt` along $X$. The sup in (7.1.22) is finite because $Y$ is compact nonempty and $\hat f$ lower semicontinuous.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 427, Theorem 7.2, with (7.1.5), (7.1.22)-(7.1.27)

import Mathlib

namespace FirstOrderOpt.ProjectionFree

open scoped RealInnerProductSpace

/-- Theorem 7.2 (the modified conditional gradient method for bilinear saddle-point problems),
Lan p. 427. Let `X ⊆ E` be compact convex, `Y ⊆ F` compact convex nonempty, `A : E → F` linear,
`f̂` convex and lower semicontinuous on `Y`, and `f(x) := max_{y ∈ Y} {⟨Ax, y⟩ - f̂(y)}` (7.1.5).
Let `ω` be a distance generating function on `Y` with modulus `σv` (strongly convex with modulus
`σv` on `Y`, differentiable along `Y`), with prox-center `c = argmin_Y ω`, prox-function
`V_Y(y) := ω(y) - ω(c) - ⟨ω'(c), y - c⟩` and `D_Y² := max_{y ∈ Y} V_Y(y)`. For a nonincreasing
sequence `η k > 0` the smooth approximations are
`fη k (x) := max_{y ∈ Y} {⟨Ax, y⟩ - f̂(y) - η k · V_Y(y)}` (7.1.22), with gradients `fηGrad k`.
The algorithm is Algorithm 7.1 with `f'(y(k-1))` replaced by `fηGrad k (y (k-1))` (7.1.26):
`x k` solves the linear optimization `min_{z ∈ X} ⟨fηGrad k (y (k-1)), z⟩`, and
`y k = (1 - α k) y (k-1) + α k x k` under either stepsize policy (7.1.9)/(7.1.10) (`hyk_le`
states what both policies guarantee: `fη k (y k) ≤ fη k (ỹ k)` for the fixed-schedule point
`ỹ k`). Then for every `k ≥ 1`, (7.1.27):
`f(y k) - f* ≤ (2/(k(k+1))) Σ_{i=1}^k [i·η(i)·D_Y² + (‖A‖²/(σv·η(i)))‖x i - y(i-1)‖²]`.

Corrected version: the smoothing `fη k` is defined from the data as in (7.1.22) — the retired
statement took each `fη k` as a free function constrained only by a sandwich, a smoothness and a
convexity hypothesis, so nothing related `fη k` to `fη (k-1)` and Lemma 7.1's monotonicity was
unavailable (the accepted disproof); `fηGrad k` is the gradient of `fη k`, and the standing
assumptions on `f̂` and `ω` are stated. -/
theorem saddle_point_cndg_rate_v2 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (X : Set E) (hXconv : Convex ℝ X) (hXcompact : IsCompact X)
    (Y : Set F) (hYconv : Convex ℝ Y) (hYcompact : IsCompact Y) (hYne : Y.Nonempty)
    (A : E →L[ℝ] F) (fhat : F → ℝ) (hfhatconv : ConvexOn ℝ Y fhat)
    (hfhatlsc : LowerSemicontinuousOn fhat Y)
    (f : E → ℝ) (hf : ∀ x, f x = sSup ((fun y => ⟪A x, y⟫ - fhat y) '' Y))
    (σv : ℝ) (hσv : 0 < σv)
    (ω : F → ℝ) (dω : F → F →L[ℝ] ℝ)
    (hωdiff : ∀ y ∈ Y, HasFDerivWithinAt ω (dω y) Y y)
    (hωstrong : ∀ y ∈ Y, ∀ z ∈ Y, ω y + (dω y) (z - y) + (σv / 2) * ‖z - y‖ ^ 2 ≤ ω z)
    (c : F) (hc : c ∈ Y) (hcmin : ∀ y ∈ Y, ω c ≤ ω y)
    (VY : F → ℝ) (hVY : ∀ y, VY y = ω y - ω c - (dω c) (y - c))
    (DY : ℝ) (hDY : 0 < DY) (hDYsq : IsLUB (VY '' Y) (DY ^ 2))
    (η : ℕ → ℝ) (hηpos : ∀ k, 1 ≤ k → 0 < η k) (hηmono : ∀ k, 1 ≤ k → η (k + 1) ≤ η k)
    (fη : ℕ → E → ℝ)
    (hfη : ∀ k x, fη k x = sSup ((fun y => ⟪A x, y⟫ - fhat y - η k * VY y) '' Y))
    (fηGrad : ℕ → E → E →L[ℝ] ℝ)
    (hηGrad : ∀ k, 1 ≤ k → ∀ x ∈ X, HasFDerivWithinAt (fη k) (fηGrad k x) X x)
    (x y : ℕ → E) (hx0 : x 0 ∈ X) (hy0 : y 0 = x 0)
    (hx : ∀ k, 1 ≤ k → x k ∈ X)
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
