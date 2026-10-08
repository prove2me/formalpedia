-- Prove2me | Theorems.Thm_BeckTeboulleMD_EMDA_theorem_4_1_a
-- name    : BeckTeboulleMD.EMDA.theorem_4_1_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:53:51.023216+00:00
-- url     : https://prove2.me/theorems/800dbdb5-6f8a-438e-ac95-465dad0a7952
-- title:
--   Theorem 4.1(a), pp. 171–172 — min_{s≤k} f(x^s) − min f ≤ [B_ψ(x*,x¹) + (2σ)⁻¹Σ t_s²‖f′(x^s)‖²_*]/Σ t_s
-- statement:
--   Suppose Assumption A holds: $X$ is a closed convex subset of a real normed space $E$; $f$ is convex on $X$ and $L_f$-Lipschitz there, $|f(x) - f(y)| \le L_f\|x - y\|$; $f$ has a minimiser $x^* \in X$; and $f'$ is a subgradient oracle on $X$. Let $\psi$ be strongly convex on $X$ with parameter $\sigma > 0$, and let $(x^k)_{k\ge1}$ be a SANP run over $X$ with step sizes $t_k > 0$. Then for every $k \ge 1$,
--   $$\min_{1 \le s \le k} f(x^s) - \min_{x \in X} f(x) \le \frac{B_\psi(x^*, x^1) + (2\sigma)^{-1}\sum_{s=1}^k t_s^2 \|f'(x^s)\|_*^2}{\sum_{s=1}^k t_s}. \tag{4.22}$$
--
--   This is the basic efficiency estimate of SANP, from which the convergence result (b) and the optimal step size of Theorem 4.2 are derived.
--
--   **Formalization Note** The constant is $(2\sigma)^{-1}$, as in (4.22), which the proof establishes ("proving (a)"); the theorem's display (4.15) prints $2\sigma^{-1}$, a weaker bound implied by this one. "$\min_{1\le s\le k} f(x^s) - \min_X f \le R$" is stated as "there is $s \in \{1, \dots, k\}$ with $f(x^s) - f(x^*) \le R$", which is equivalent since the minimum over a finite set is attained and $\min_X f = f(x^*)$. $\|\cdot\|_*$ is the operator norm. "$X$ with nonempty interior" and "$x^1 \in \operatorname{int} X$" are replaced by the SANP run, which encodes the paper's assumption that the sequence is well defined; this covers $X = \Delta$, whose interior in $\mathbb R^n$ is empty.
-- source:
--   Beck & Teboulle, Mirror descent and nonlinear projected subgradient methods for convex optimization, Oper. Res. Lett. 31 (2003), pp. 171–172, Theorem 4.1(a), (4.15), in the form (4.22); Assumption A p. 167

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

namespace BeckTeboulleMD.EMDA

/-- Theorem 4.1(a), pp. 171–172, in the form (4.22): under Assumption A, for a SANP run and every
`k ≥ 1`,
`min_{1≤s≤k} f(x^s) − min_X f ≤ [B_ψ(x*, x¹) + (2σ)⁻¹ ∑_{s=1}^k t_s² ‖f′(x^s)‖²_*] / ∑_{s=1}^k t_s`. -/
theorem theorem_4_1_a {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : E → ℝ) (hf : ConvexOn ℝ X f)
    (Lf : ℝ) (hLip : ∀ x ∈ X, ∀ y ∈ X, |f x - f y| ≤ Lf * ‖x - y‖)
    (xstar : E) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    (g : E → E →L[ℝ] ℝ) (hg : ∀ x ∈ X, ∀ y ∈ X, f x + g x (y - x) ≤ f y)
    (ψ : E → ℝ) (σ : ℝ) (hσ : 0 < σ) (hψ : StrongConvexOn X σ ψ)
    (t : ℕ → ℝ) (x : ℕ → E) (hrun : IsSANPRun X ψ g t x) :
    ∀ k, 1 ≤ k → ∃ s ∈ Finset.Icc 1 k, f (x s) - f xstar
      ≤ (bregman ψ xstar (x 1)
          + 1 / (2 * σ) * ∑ s ∈ Finset.Icc 1 k, t s ^ 2 * ‖g (x s)‖ ^ 2)
        / ∑ s ∈ Finset.Icc 1 k, t s := by sorry

end BeckTeboulleMD.EMDA
