-- Prove2me | Theorems.Thm_DualMirrorAlloc_proposition_5
-- name    : DualMirrorAlloc.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:02:40.582776+00:00
-- url     : https://prove2.me/theorems/378b00b7-2f3e-4189-9260-9ea4fec194d2
-- title:
--   Proposition 5, (48), p.59 — regret of online mirror descent on a convex set
-- statement:
--   Let $D\subseteq\mathbb R^m$ be convex, $\eta>0$, $\sigma>0$, and let $h$ be $\sigma$-strongly convex in $\|\cdot\|_1$ on $D$. Let $w_1,w_2,\dots$ be convex functions on $D$ and $\mu_1,\mu_2,\dots\in D$, with $g_t$ a subgradient of $w_t$ at $\mu_t$ relative to $D$ (that is, $w_t(\nu)\ge w_t(\mu_t)+g_t^\top(\nu-\mu_t)$ for $\nu\in D$) and $\|g_t\|_\infty\le G$. Suppose $h$ is differentiable within $D$ at $\mu_1,\dots,\mu_{T+1}$ and, for $t=1,\dots,T$,
--   $$
--   \mu_{t+1}\in\arg\min_{\mu\in D}\ g_t^\top\mu+\frac1\eta V_h(\mu,\mu_t).
--   $$
--   Then for every $\mu\in D$,
--   $$
--   \sum_{t=1}^T\big(w_t(\mu_t)-w_t(\mu)\big)\le\frac{G^2\eta}{2\sigma}T+\frac1\eta V_h(\mu,\mu_1).
--   $$
--
--   This is the standard online mirror descent bound, in the form needed by Theorem 1: an arbitrary convex domain, $\ell_1$ strong convexity and an $\ell_\infty$ bound on the subgradients.
--
--   **Formalization Note** $V_h$ uses the derivative of $h$ within $D$. Time is 1-based as on the page. The functions $w_t$ are typed on $\mathbb R^m$; only their values on $D$ matter.
--
--   Differences from the source:
--   - reading: η, σ (no sign stated) → 0 < η and 0 < σ; reason: the bound divides by η and σ; a step size and a strong-convexity modulus are positive
--   - reading: the iterates µ_t (µ_1 implicitly in D) → µ_t ∈ D for every t; reason: the arg min is over D and the comparison point µ_1 is an iterate of the method on D
--   - generalization: h differentiable (∇h used) and σ-strongly convex on D → h differentiable within D at the iterates µ_1, …, µ_{T+1} only; strong convexity required at points where the derivative within D exists; reason: the proof evaluates ∇h only at the iterates; a differentiable σ-strongly convex h satisfies both hypotheses, so the statement specializes to the page's
--   - encoding: ∇h(y) in V_h → fderivWithin ℝ h D y; reason: the derivative of h within the domain D; it agrees with the gradient in every direction of D − D
--   - encoding: g_t ∈ ∂_µ w_t(µ_t), ‖g_t‖∞ ≤ G → w_t(ν) ≥ w_t(µ_t) + g_tᵀ(ν − µ_t) for ν ∈ D; |g_{t,j}| ≤ G for all j; reason: subgradient of w_t : D → ℝ, and the definition of the sup norm
--   - encoding: µ_{t+1} = arg min_{µ∈D} → µ_{t+1} is a minimizer over D (any minimizer); reason: the arg min is a choice of minimizer
--   - encoding: finite sequences w_t, g_t, µ_t (t = 1, …, T + 1) on D → sequences indexed by t ∈ ℕ, with convexity, the subgradient inequality, |g_{t,j}| ≤ G and µ_t ∈ D required at every t ∈ ℕ; reason: the extra indices are irrelevant: any finite instance extends by w_t = 0, g_t = 0, µ_t = µ_1 outside 1, …, T + 1 (and G may be taken ≥ 0, which does not change the bound when T = 0)
-- source:
--   Balseiro–Lu–Mirrokni, The Best of Many Worlds: Dual Mirror Descent for Online Allocation Problems, arXiv:2011.10124v3, Appendix G, Proposition 5, (48), p.59 (proof pp.59–60)

import Mathlib
import Definitions.Def_DualMirrorAlloc_Bregman

namespace DualMirrorAlloc

/-- **Proposition 5 (online mirror descent).** Balseiro–Lu–Mirrokni, arXiv:2011.10124v3,
Proposition 5, (48), p.59: "Consider the sequence of convex functions wt : D → R with D ⊆ Rm a
convex set. Let gt ∈ ∂µwt(µt) be a sub-gradient and µt+1 = arg min_{µ∈D} gtᵀµ + (1/η)Vh(µ, µt).
Suppose sub-gradients are bounded by ∥gt∥∞ ≤ G and the reference function h is σ-strongly convex
with respect to ∥·∥1-norm. Then, for every µ ∈ D we have
Σ_{t=1}^{T} wt(µt) − wt(µ) ≤ (G²η/2σ) T + (1/η)Vh(µ, µ1)."

**Formalization Note.**
- Time is 1-based as on the page: the iterates `µ_1, …, µ_{T+1}` are `mu 1, …, mu (T+1)`.
- `g_t ∈ ∂w_t(µ_t)` is a subgradient of `w_t : D → ℝ` relative to `D`:
  `w_t(ν) ≥ w_t(µ_t) + g_tᵀ(ν − µ_t)` for `ν ∈ D`. `‖g_t‖∞ ≤ G` is `|g_{t,j}| ≤ G` for every `j`.
- `V_h` is the Bregman divergence with `∇h` the derivative of `h` within `D`
  (`bregman D h`); `σ`-strong convexity in `‖·‖₁` is `IsStronglyConvexL1 D h σ` (at points where
  `∇h` exists).
- Implicit on the page and made explicit: `η > 0`, `σ > 0`, `µ_1 ∈ D` (the iterates lie in `D`),
  and `h` differentiable within `D` at the iterates `µ_1, …, µ_{T+1}` where `∇h` is evaluated. -/
theorem proposition_5 {m : ℕ} (D : Set (Fin m → ℝ)) (hD : Convex ℝ D)
    (h : (Fin m → ℝ) → ℝ) (σ : ℝ) (hσ : 0 < σ) (hsc : IsStronglyConvexL1 D h σ)
    (η : ℝ) (hη : 0 < η) (G : ℝ)
    (w : ℕ → (Fin m → ℝ) → ℝ) (hw : ∀ t, ConvexOn ℝ D (w t))
    (mu g : ℕ → Fin m → ℝ) (hmuD : ∀ t, mu t ∈ D)
    (hg : ∀ t, ∀ ν ∈ D, w t (mu t) + g t ⬝ᵥ (ν - mu t) ≤ w t ν)
    (hG : ∀ t, ∀ j, |g t j| ≤ G)
    (T : ℕ)
    (hdiff : ∀ t ∈ Finset.Icc 1 (T + 1), DifferentiableWithinAt ℝ h D (mu t))
    (hstep : ∀ t ∈ Finset.Icc 1 T, ∀ ν ∈ D,
      g t ⬝ᵥ mu (t + 1) + bregman D h (mu (t + 1)) (mu t) / η ≤ g t ⬝ᵥ ν + bregman D h ν (mu t) / η) :
    ∀ ν ∈ D, ∑ t ∈ Finset.Icc 1 T, (w t (mu t) - w t ν) ≤
      G ^ 2 * η / (2 * σ) * T + bregman D h ν (mu 1) / η := by sorry

end DualMirrorAlloc
