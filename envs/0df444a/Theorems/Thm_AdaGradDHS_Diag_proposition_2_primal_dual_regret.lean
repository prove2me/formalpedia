-- Prove2me | Theorems.Thm_AdaGradDHS_Diag_proposition_2_primal_dual_regret
-- name    : AdaGradDHS.Diag.proposition_2_primal_dual_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:22:51.721318+00:00
-- url     : https://prove2.me/theorems/06386de4-d481-4cb8-8563-072027dbaa2c
-- title:
--   Proposition 2: regret of the primal-dual update (3) (corrected: $x_1$ also minimizes $\psi_0$ over $X$, with $\psi_0(x_1) \ge 0$)
-- statement:
--   Throughout, $\langle\cdot,\cdot\rangle$ is the Euclidean inner product on $\mathbb{R}^d$. Let
--
--   1. $X \subseteq \mathbb{R}^d$ be convex and $\varphi : \mathbb{R}^d \to \mathbb{R}$ convex on $X$, and $\eta > 0$;
--   2. $\psi_0, \psi_1, \dots$ be proximal functions such that, for $t = 0, \dots, T-1$, $\psi_t$ is 1-strongly convex on $X$ with respect to a seminorm $\|\cdot\|_{\psi_t}$ and $\psi_t \le \psi_{t+1}$ on $X$;
--   3. $x_1, \dots, x_{T+1}$ be a run of the primal-dual subgradient update (3), $x_{t+1} \in \operatorname{argmin}_{x \in X}\{\eta\langle \bar g_t, x\rangle + \eta\varphi(x) + \tfrac1t\psi_t(x)\}$, whose initial point $x_1 \in X$ minimizes $\varphi$ over $X$, minimizes $\psi_0$ over $X$, and satisfies $\psi_0(x_1) \ge 0$;
--   4. $g_t$ satisfy $f_t(x_t) + \langle g_t, y - x_t\rangle \le f_t(y)$ for all $y \in X$ (e.g. $g_t \in \partial f_t(x_t)$), and $G_t \ge \|g_t\|_{\psi^*_{t-1}}$ in the sense $\langle g_t, v\rangle \le G_t\|v\|_{\psi_{t-1}}$ for all $v$, for $t = 1, \dots, T$.
--
--   Then for every $x^* \in X$,
--   $$\sum_{t=1}^T \big[f_t(x_t) + \varphi(x_t) - f_t(x^*) - \varphi(x^*)\big] \le \frac1\eta \psi_T(x^*) + \frac\eta2 \sum_{t=1}^T G_t^2 .$$
--
--   This is the regret bound (10) of regularized dual averaging with time-varying proximal functions; with AdaGrad's $\psi_t$ it yields the primal-dual clause of Theorem 5.
--
--   **Formalization Note** The printed proposition does not require $x_1$ to minimize $\psi_0$, but its proof ends with "$x_1 = \operatorname{argmin}_{x\in X}\varphi(x)$ and $\psi_0^*(0) = 0$", which uses that $x_1 = \nabla\psi_0^*(0)$ minimizes $\psi_0$ and that $\psi_0^*(0) = -\psi_0(x_1)/\eta \le 0$. Without these the statement fails (see the correction below).
--
--   Differences from the source:
--   - correction: x_1 = argmin_{x∈X} ϕ(x), nothing on ψ_0 → additionally ∀ y ∈ X, ψ 0 (x 1) ≤ ψ 0 y and 0 ≤ ψ 0 (x 1); reason: false without them: d = 1, ψ_t(x) = x²/2, ‖·‖ = |·|, X = ℝ, ϕ(x) = |x − 1000| (x_1 = 1000), f_1(x) = 2x, η = 1, T = 1, x* = 0 give LHS = 1000 > 2 = RHS; the proof's last line uses exactly these two facts (ψ*_0(0) = 0 with x_1 = ∇ψ*_0(0))
--   - reading: "the sequence {x_t} defined by the update (3)" and the §2 standing assumptions (ψ_t monotone, 1-strongly convex w.r.t. a semi-norm) → hx1φ (x_1 minimizes φ over X, p. 2123) and hypotheses hsc, hmono for t = 0, …, T − 1; reason: the update (3) is defined with x_1 = argmin_{x∈X} ϕ(x); the standing assumptions are stated for the indices the bound uses
--   - generalization: ψ_t 1-strongly convex w.r.t. a semi-norm (ψ(y) ≥ ψ(x) + ⟨∇ψ(x), y − x⟩ + ½‖x − y‖²_ψ for all x, y) → the same inequality only for x, y ∈ X, with ψ_t differentiable at the points of X (IsOneStronglyConvexWrt); reason: a function strongly convex on ℝ^d satisfies it; only points of X are used
--   - generalization: X a (closed) convex set, ϕ a (closed) convex function (pp. 2122–2123) → X any convex set (ConvexOn ℝ X φ), not necessarily closed; φ : ℝ^d → ℝ convex on X; reason: closedness only guarantees that the argmins exist, which the run hypothesis carries; an extended-valued closed convex ϕ is covered by replacing X with X ∩ dom ϕ
--   - generalization: f_t (closed) convex and g_t ∈ ∂f_t(x_t) → f_t arbitrary, g_t with f_t(x_t) + ⟨g_t, y − x_t⟩ ≤ f_t(y) for all y ∈ X (IsSubgradFeedback); reason: only the subgradient inequality on X is used; every convex f_t with g_t ∈ ∂f_t(x_t) satisfies it
--   - encoding: x_{t+1} = argmin_{x∈X} {η⟨ḡ_t, x⟩ + ηϕ(x) + (1/t)ψ_t(x)} → x (t+1) ∈ X is a minimizer of this objective over X for t = 1, …, T (IsPrimalDualRun); reason: existence is the paper's presupposition (the sequence defined by the update); where the minimizer is not unique any minimizer is allowed
--   - encoding: ‖f′_t(x_t)‖²_{ψ*} (dual seminorm, possibly +∞) → G_t ^ 2 with ⟨g_t, v⟩ ≤ G_t · n(v) for all v (IsDualBound); reason: G_t = the dual norm recovers the paper when it is finite; when it is +∞ no real G_t exists and the paper's bound is vacuous as well
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), §2, p. 2129, Proposition 2, eq. (10) (proof: Appendix F, pp. 2152–2153); standing assumptions §2, p. 2129; update (3) and x1 = argmin ϕ, p. 2123

import Mathlib
import Definitions.Def_AdaGradDHS_Diag_IsOneStronglyConvexWrt
import Definitions.Def_AdaGradDHS_Diag_IsDualBound
import Definitions.Def_AdaGradDHS_Diag_IsSubgradFeedback
import Definitions.Def_AdaGradDHS_Diag_IsPrimalDualRun
import Definitions.Def_AdaGradDHS_Diag_regret

namespace AdaGradDHS.Diag

/-- **Proposition 2: regret of the primal-dual subgradient update (3) with time-varying proximal
functions (corrected: `x_1` also minimizes `ψ_0` over `X`, with `ψ_0(x_1) ≥ 0`).**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), §2, p. 2129, Proposition 2 (proof: Appendix F, pp. 2152–2153): "Let the sequence {xt} be
defined by the update (3). For any x∗ ∈ X, Σ_{t=1}^T ft(xt) + ϕ(xt) − ft(x∗) − ϕ(x∗) ≤
(1/η)ψT(x∗) + (η/2) Σ_{t=1}^T ‖f′t(xt)‖²ψ∗t−1. (10)"
Standing assumptions (§2, p. 2129): "We assume that ψt is monotonically non-decreasing, that is,
ψt+1(x) ≥ ψt(x). We also assume that ψt is 1-strongly convex with respect to a time-dependent
semi-norm ‖·‖ψt." Update (3), p. 2123: "x1 = argmin_{x∈X} ϕ(x)".

Let `X ⊆ ℝ^d`, `φ` convex on `X`, `η > 0`, `T ∈ ℕ`; let `ψ_0, …, ψ_{T−1}` be 1-strongly convex on `X`
w.r.t. seminorms `n_0, …, n_{T−1}`, with `ψ_t ≤ ψ_{t+1}` on `X` for `t < T`. Let `x_2, …, x_{T+1}`
be generated by (3) from `x_1 ∈ X`, where `x_1` minimizes `φ` over `X`, minimizes `ψ_0` over `X`,
and `ψ_0(x_1) ≥ 0`. Let `g_t` satisfy the subgradient inequality of `f_t` at `x_t` on `X` and let
`⟨g_t, v⟩ ≤ G_t n_{t−1}(v)` for all `v` (`t = 1, …, T`). Then for every `x* ∈ X`,
`R_φ(T) ≤ (1/η) ψ_T(x*) + (η/2) Σ_{t=1}^T G_t²`.

**Formalization Note.** The printed proposition is false without the condition on `ψ_0`:
`d = 1`, `ψ_t(x) = x²/2` for all `t`, `n = |·|`, `X = ℝ`, `φ(x) = |x − 1000|` (so `x_1 = 1000`),
`f_1(x) = 2x`, `η = 1`, `T = 1`, `x* = 0` give `R_φ(1) = 1000 > 2 = (1/η)ψ_1(0) + (η/2)·2²`. The
proof's last line ("Recalling that x1 = argmin_{x∈X}{ϕ(x)} and that ψ∗0(0) = 0") uses that
`x_1 = ∇ψ*_0(0)` minimizes `ψ_0` over `X` and that `ψ*_0(0) = −ψ_0(x_1)/η` is at most `0`; `hx1ψ`
and `hψ0` state exactly these two facts (`hψ0` is weaker than the printed `ψ*_0(0) = 0`). The standing assumptions are hypotheses
for the indices used (`t = 0, …, T−1` for strong convexity, `t < T` for monotonicity), on `X`
only. Dual norms enter through `IsDualBound` (`‖g_t‖_{ψ*_{t−1}} ≤ G_t`); `t − 1` is used only for
`t ≥ 1`. `X` need not be closed and `f_t` need not be convex. -/
theorem proposition_2_primal_dual_regret {d : ℕ} {X : Set (EuclideanSpace ℝ (Fin d))} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ConvexOn ℝ X φ) {η : ℝ} (hη : 0 < η) {ψ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ}
    {n : ℕ → Seminorm ℝ (EuclideanSpace ℝ (Fin d))} {T : ℕ}
    (hsc : ∀ t < T, IsOneStronglyConvexWrt X (ψ t) (n t))
    (hmono : ∀ t < T, ∀ y ∈ X, ψ t y ≤ ψ (t + 1) y)
    {f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ} {g x : ℕ → EuclideanSpace ℝ (Fin d)} (hrun : IsPrimalDualRun X φ ψ η g x T)
    (hx1φ : ∀ y ∈ X, φ (x 1) ≤ φ y)
    (hx1ψ : ∀ y ∈ X, ψ 0 (x 1) ≤ ψ 0 y) (hψ0 : 0 ≤ ψ 0 (x 1))
    (hfb : IsSubgradFeedback X f g x T)
    {G : ℕ → ℝ} (hG : ∀ t ∈ Finset.Icc 1 T, IsDualBound (n (t - 1)) (g t) (G t))
    {xstar : EuclideanSpace ℝ (Fin d)} (hxstar : xstar ∈ X) :
    regret f φ x xstar T ≤ 1 / η * ψ T xstar + η / 2 * ∑ t ∈ Finset.Icc 1 T, G t ^ 2 := by sorry

end AdaGradDHS.Diag
