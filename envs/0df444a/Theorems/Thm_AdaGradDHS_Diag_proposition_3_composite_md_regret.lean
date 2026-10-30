-- Prove2me | Theorems.Thm_AdaGradDHS_Diag_proposition_3_composite_md_regret
-- name    : AdaGradDHS.Diag.proposition_3_composite_md_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:24:06.865386+00:00
-- url     : https://prove2.me/theorems/6268934d-5ec4-49e8-91bd-2c070cf552d0
-- title:
--   Proposition 3: regret of composite mirror descent (4) (corrected: $x_1$ minimizes $\varphi$ over $X$)
-- statement:
--   Throughout, $\langle\cdot,\cdot\rangle$ is the Euclidean inner product on $\mathbb{R}^d$. Let
--
--   1. $X \subseteq \mathbb{R}^d$ be convex, $\varphi : \mathbb{R}^d \to \mathbb{R}$ convex on $X$, $\eta > 0$ and $T \ge 1$;
--   2. $\psi_1, \dots, \psi_T$ be 1-strongly convex on $X$ with respect to seminorms $\|\cdot\|_{\psi_1}, \dots, \|\cdot\|_{\psi_T}$;
--   3. $x_1, \dots, x_{T+1}$ be a run of the composite mirror-descent update (4), $x_{t+1} \in \operatorname{argmin}_{x\in X}\{\eta\langle g_t, x\rangle + \eta\varphi(x) + B_{\psi_t}(x, x_t)\}$, whose initial point $x_1 \in X$ minimizes $\varphi$ over $X$;
--   4. $g_t$ satisfy $f_t(x_t) + \langle g_t, y - x_t\rangle \le f_t(y)$ for all $y \in X$, and $\langle g_t, v\rangle \le G_t\|v\|_{\psi_t}$ for all $v$ ($\|g_t\|_{\psi_t^*} \le G_t$), for $t = 1, \dots, T$.
--
--   Then for every $x^* \in X$,
--   $$\sum_{t=1}^T \big[f_t(x_t) + \varphi(x_t) - f_t(x^*) - \varphi(x^*)\big] \le \frac1\eta B_{\psi_1}(x^*, x_1) + \frac1\eta\sum_{t=1}^{T-1}\Big[B_{\psi_{t+1}}(x^*, x_{t+1}) - B_{\psi_t}(x^*, x_{t+1})\Big] + \frac\eta2\sum_{t=1}^T G_t^2 .$$
--
--   This is the regret bound (11) of composite mirror descent with time-varying proximal functions; with AdaGrad's $\psi_t$ it yields the mirror-descent clause of Theorem 5.
--
--   **Formalization Note** The printed "Assume w.l.o.g. that $\varphi(x_1) = 0$" is replaced by "$x_1$ minimizes $\varphi$ over $X$" (p. 2123, $x_1 = \operatorname{argmin}_{x\in X}\varphi(x)$). Shifting $\varphi$ by a constant changes neither the updates nor the regret, so the normalization $\varphi(x_1) = 0$ is immaterial once $x_1$ is a minimizer.
--
--   Differences from the source:
--   - correction: "Assume w.l.o.g. that ϕ(x_1) = 0" → ∀ y ∈ X, φ (x 1) ≤ φ y; reason: false as printed: d = 1, ψ_t(x) = x²/2, X = [−1, 1], ϕ(x) = x, x_1 = 0 (ϕ(x_1) = 0), f_t ≡ 0, g_t = 0, η = 1, T = 2, x* = −1 give x_2 = −1 and LHS = 1 > ½ = RHS; the proof (a sum of Lemma 16) needs ϕ(x_1) ≤ ϕ(x_{T+1}), and normalizing a minimizer to value 0 is immaterial
--   - encoding: rounds t = 1, …, T → 1 ≤ T; reason: the right side involves ψ_1 and x_1, about which nothing is assumed when T = 0; the paper's statement concerns T ≥ 1 rounds
--   - generalization: §2 standing assumptions: ψ_t monotone and 1-strongly convex w.r.t. a semi-norm on ℝ^d → only strong convexity of ψ_1, …, ψ_T on X (IsOneStronglyConvexWrt); no monotonicity; reason: the proof, a sum of Lemma 16, does not use monotonicity; functions strongly convex on ℝ^d satisfy the hypothesis
--   - generalization: X a (closed) convex set, ϕ a (closed) convex function (pp. 2122–2123) → X any convex set (ConvexOn ℝ X φ), not necessarily closed; φ : ℝ^d → ℝ convex on X; reason: closedness only guarantees that the argmins exist, which the run hypothesis carries; an extended-valued closed convex ϕ is covered by replacing X with X ∩ dom ϕ
--   - generalization: f_t (closed) convex and g_t ∈ ∂f_t(x_t) → f_t arbitrary, g_t with f_t(x_t) + ⟨g_t, y − x_t⟩ ≤ f_t(y) for all y ∈ X (IsSubgradFeedback); reason: only the subgradient inequality on X is used; every convex f_t with g_t ∈ ∂f_t(x_t) satisfies it
--   - encoding: x_{t+1} = argmin_{x∈X} {η⟨g_t, x⟩ + ηϕ(x) + B_{ψ_t}(x, x_t)} → x (t+1) ∈ X is a minimizer of this objective over X for t = 1, …, T (IsCompositeMDRun); reason: existence is the paper's presupposition (the sequence defined by the update); where the minimizer is not unique any minimizer is allowed
--   - encoding: ‖f′_t(x_t)‖²_{ψ*} (dual seminorm, possibly +∞) → G_t ^ 2 with ⟨g_t, v⟩ ≤ G_t · n(v) for all v (IsDualBound); reason: G_t = the dual norm recovers the paper when it is finite; when it is +∞ no real G_t exists and the paper's bound is vacuous as well
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), §2, p. 2129, Proposition 3, eq. (11) (proof: Appendix F, p. 2154); standing assumption §2, p. 2129; x1 = argmin ϕ, p. 2123

import Mathlib
import Definitions.Def_AdaGradDHS_Diag_bregman
import Definitions.Def_AdaGradDHS_Diag_IsOneStronglyConvexWrt
import Definitions.Def_AdaGradDHS_Diag_IsDualBound
import Definitions.Def_AdaGradDHS_Diag_IsSubgradFeedback
import Definitions.Def_AdaGradDHS_Diag_IsCompositeMDRun
import Definitions.Def_AdaGradDHS_Diag_regret

namespace AdaGradDHS.Diag

/-- **Proposition 3: regret of composite mirror descent (4) with time-varying proximal functions
(corrected: `x_1` minimizes `φ` over `X`).**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), §2, p. 2129, Proposition 3 (proof: Appendix F, p. 2154, "Sum the equation in the conclusion
of Lemma 16"): "Let the sequence {xt} be defined by the update (4). Assume w.l.o.g. that
ϕ(x1) = 0. For any x∗ ∈ X, Σ_{t=1}^T ft(xt) + ϕ(xt) − ft(x∗) − ϕ(x∗) ≤ (1/η)Bψ1(x∗, x1) + (1/η)
Σ_{t=1}^{T−1} [Bψt+1(x∗, xt+1) − Bψt(x∗, xt+1)] + (η/2) Σ_{t=1}^T ‖f′t(xt)‖²ψ∗t. (11)"
Standing assumption (§2, p. 2129): ψt is 1-strongly convex w.r.t. a semi-norm ‖·‖ψt.

Let `X ⊆ ℝ^d`, `φ` convex on `X`, `η > 0`, `T ≥ 1`; let `ψ_1, …, ψ_T` be 1-strongly convex on `X`
w.r.t. seminorms `n_1, …, n_T`. Let `x_2, …, x_{T+1}` be generated by (4) from `x_1 ∈ X`, where `x_1`
minimizes `φ` over `X`. Let `g_t` satisfy the subgradient inequality of `f_t` at `x_t` on `X`, and
`⟨g_t, v⟩ ≤ G_t n_t(v)` for all `v` (`t = 1, …, T`). Then for every `x* ∈ X`,
`R_φ(T) ≤ (1/η)B_{ψ_1}(x*, x_1) + (1/η)Σ_{t=1}^{T−1}[B_{ψ_{t+1}}(x*, x_{t+1}) − B_{ψ_t}(x*, x_{t+1})]
+ (η/2)Σ_{t=1}^T G_t²`.

**Formalization Note.** The printed "Assume w.l.o.g. that ϕ(x1) = 0" is replaced by "x_1 minimizes
φ over X" (the update (3)/(4) setting of p. 2123, "x1 = argmin_{x∈X} ϕ(x)"): with only `φ(x_1) = 0`
the proposition is false (`d = 1`, `ψ_t(x) = x²/2`, `X = [−1, 1]`, `φ(x) = x`, `x_1 = 0`,
`f_t ≡ 0`, `g_t = 0`, `η = 1`, `T = 2`, `x* = −1`: `x_2 = −1`, `R_φ(2) = 1 > ½` = right side). Since
shifting `φ` by a constant changes neither the updates nor the regret, the normalization
`φ(x_1) = 0` is immaterial. `T ≥ 1` is the range of rounds (the right side involves `ψ_1`).
Monotonicity of `ψ_t` is not needed. Strong convexity is on `X` w.r.t. seminorms; dual norms
enter through `IsDualBound`; `X` need not be closed; `f_t` need not be convex. -/
theorem proposition_3_composite_md_regret {d : ℕ} {X : Set (EuclideanSpace ℝ (Fin d))} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ConvexOn ℝ X φ) {η : ℝ} (hη : 0 < η) {ψ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ}
    {n : ℕ → Seminorm ℝ (EuclideanSpace ℝ (Fin d))} {T : ℕ} (hT : 1 ≤ T)
    (hsc : ∀ t ∈ Finset.Icc 1 T, IsOneStronglyConvexWrt X (ψ t) (n t))
    {f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ} {g x : ℕ → EuclideanSpace ℝ (Fin d)} (hrun : IsCompositeMDRun X φ ψ η g x T)
    (hx1φ : ∀ y ∈ X, φ (x 1) ≤ φ y)
    (hfb : IsSubgradFeedback X f g x T)
    {G : ℕ → ℝ} (hG : ∀ t ∈ Finset.Icc 1 T, IsDualBound (n t) (g t) (G t))
    {xstar : EuclideanSpace ℝ (Fin d)} (hxstar : xstar ∈ X) :
    regret f φ x xstar T ≤
      1 / η * bregman (ψ 1) xstar (x 1) +
        1 / η * ∑ t ∈ Finset.Ico 1 T,
          (bregman (ψ (t + 1)) xstar (x (t + 1)) - bregman (ψ t) xstar (x (t + 1))) +
        η / 2 * ∑ t ∈ Finset.Icc 1 T, G t ^ 2 := by sorry

end AdaGradDHS.Diag
