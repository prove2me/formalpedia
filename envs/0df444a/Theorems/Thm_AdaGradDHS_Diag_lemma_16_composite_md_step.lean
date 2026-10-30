-- Prove2me | Theorems.Thm_AdaGradDHS_Diag_lemma_16_composite_md_step
-- name    : AdaGradDHS.Diag.lemma_16_composite_md_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:23:25.294869+00:00
-- url     : https://prove2.me/theorems/ce275120-f156-4f59-84b6-76f59bd9348b
-- title:
--   Lemma 16: one step of composite mirror descent (4)
-- statement:
--   Let $X \subseteq \mathbb{R}^d$ be convex, $\varphi : \mathbb{R}^d \to \mathbb{R}$ convex on $X$, $\eta > 0$, and let $\psi$ be 1-strongly convex on $X$ with respect to a seminorm $\|\cdot\|_\psi$. Let $x_t, x_{t+1} \in X$, where
--   $$x_{t+1} \in \operatorname*{argmin}_{x \in X} \big\{\eta\langle g, x\rangle + \eta\varphi(x) + B_\psi(x, x_t)\big\}.$$
--   Let $x^* \in X$ with $f(x_t) + \langle g, x^* - x_t\rangle \le f(x^*)$ (e.g. $g = f'(x_t) \in \partial f(x_t)$), and let $G$ satisfy $\langle g, v\rangle \le G\|v\|_\psi$ for all $v$ (i.e. $\|g\|_{\psi^*} \le G$). Then
--   $$\eta\big(f(x_t) - f(x^*)\big) + \eta\big(\varphi(x_{t+1}) - \varphi(x^*)\big) \le B_\psi(x^*, x_t) - B_\psi(x^*, x_{t+1}) + \frac{\eta^2}{2} G^2 .$$
--
--   Summing this one-step inequality over $t = 1, \dots, T$ proves Proposition 3.
--
--   **Formalization Note** The step is stated for one round from any $x_t \in X$. The paper's "for any $x^*$" is read as $x^* \in X$, the range of the optimality condition (32) used in its proof.
--
--   Differences from the source:
--   - reading: "for any x∗" → xstar ∈ X; reason: the proof applies the optimality condition (32), valid for all x ∈ X, "in particular … for x = x∗"
--   - generalization: x_t, x_{t+1} consecutive iterates of (4), B_{ψ_t} strongly convex w.r.t. a norm, f_t convex → one step from any x_t ∈ X; ψ 1-strongly convex on X w.r.t. a seminorm (IsOneStronglyConvexWrt); only f(x_t) + ⟨g, x* − x_t⟩ ≤ f(x*); reason: the paper's setting satisfies every hypothesis; the proof uses nothing more
--   - generalization: X a (closed) convex set, ϕ a (closed) convex function (pp. 2122–2123) → X any convex set (ConvexOn ℝ X φ), not necessarily closed; φ : ℝ^d → ℝ convex on X; reason: closedness only guarantees that the argmins exist, which the run hypothesis carries; an extended-valued closed convex ϕ is covered by replacing X with X ∩ dom ϕ
--   - encoding: ‖f′_t(x_t)‖²_{ψ*} (dual seminorm, possibly +∞) → G_t ^ 2 with ⟨g_t, v⟩ ≤ G_t · n(v) for all v (IsDualBound); reason: G_t = the dual norm recovers the paper when it is finite; when it is +∞ no real G_t exists and the paper's bound is vacuous as well
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), Appendix F, p. 2154, Lemma 16

import Mathlib
import Definitions.Def_AdaGradDHS_Diag_bregman
import Definitions.Def_AdaGradDHS_Diag_IsOneStronglyConvexWrt
import Definitions.Def_AdaGradDHS_Diag_IsDualBound

namespace AdaGradDHS.Diag

/-- **Lemma 16: one step of composite mirror descent (4).**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), Appendix F, p. 2154, Lemma 16: "Let {xt} be the sequence defined by the update (4) and
assume that Bψt(·,·) is strongly convex with respect to a norm ‖·‖ψt. Let ‖·‖ψ∗t be the associated
dual norm. Then for any x∗, η(ft(xt) − ft(x∗)) + η(ϕ(xt+1) − ϕ(x∗)) ≤ Bψt(x∗, xt) − Bψt(x∗, xt+1)
+ (η²/2)‖f′t(xt)‖²ψ∗t".

Let `X ⊆ ℝ^d`, `φ` convex on `X`, `η > 0`, and `ψ` 1-strongly convex on `X` w.r.t. a seminorm `n`.
Let `x_t, x_{t+1} ∈ X`, where `x_{t+1}` minimizes `η⟨g, x⟩ + ηφ(x) + B_ψ(x, x_t)` over `x ∈ X`.
If `f(x_t) + ⟨g, x* − x_t⟩ ≤ f(x*)` for some `x* ∈ X`, and `⟨g, v⟩ ≤ G n(v)` for all `v`, then
`η(f(x_t) − f(x*)) + η(φ(x_{t+1}) − φ(x*)) ≤ B_ψ(x*, x_t) − B_ψ(x*, x_{t+1}) + (η²/2) G²`.

**Formalization Note.** "For any x∗" is read as `x* ∈ X`: the proof applies the optimality
condition (32), valid "for all x ∈ X", "in particular … for x = x∗". The step is stated for one
round from any `x_t ∈ X`; strong convexity of `B_ψ` w.r.t. `n` is the paper's §2 notion
(`IsOneStronglyConvexWrt`, required on `X` only, with a seminorm in place of the norm); the
subgradient `f′_t(x_t)` is any `g` satisfying the subgradient inequality at `x*` (no convexity of
`f`); `‖g‖_{ψ*} ≤ G` is `IsDualBound n g G`. `X` need not be closed. -/
theorem lemma_16_composite_md_step {d : ℕ} {X : Set (EuclideanSpace ℝ (Fin d))} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ConvexOn ℝ X φ) {η : ℝ} (hη : 0 < η) {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {n : Seminorm ℝ (EuclideanSpace ℝ (Fin d))} (hsc : IsOneStronglyConvexWrt X ψ n)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {g xt xnext xstar : EuclideanSpace ℝ (Fin d)} (hxt : xt ∈ X) (hxnext : xnext ∈ X)
    (hmin : ∀ y ∈ X, η * inner ℝ g xnext + η * φ xnext + bregman ψ xnext xt ≤
      η * inner ℝ g y + η * φ y + bregman ψ y xt)
    (hsub : f xt + inner ℝ g (xstar - xt) ≤ f xstar) (hxstar : xstar ∈ X)
    {G : ℝ} (hG : IsDualBound n g G) :
    η * (f xt - f xstar) + η * (φ xnext - φ xstar) ≤
      bregman ψ xstar xt - bregman ψ xstar xnext + η ^ 2 / 2 * G ^ 2 := by sorry

end AdaGradDHS.Diag
