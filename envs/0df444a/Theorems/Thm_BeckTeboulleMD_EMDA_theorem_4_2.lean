-- Prove2me | Theorems.Thm_BeckTeboulleMD_EMDA_theorem_4_2
-- name    : BeckTeboulleMD.EMDA.theorem_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:54:00.396135+00:00
-- url     : https://prove2.me/theorems/6d7d2a5d-7d40-45bb-87f9-931c4204978b
-- title:
--   Theorem 4.2, p. 172 — with t_k = √(2σB_ψ(x*,x¹))/(L_f√k), min_{s≤k} f(x^s) − min f ≤ L_f√(2B_ψ(x*,x¹)/σ)/√k
-- statement:
--   Suppose Assumption A holds ($X$ closed convex in a real normed space $E$; $f$ convex and $L_f$-Lipschitz on $X$ with $L_f > 0$; a minimiser $x^* \in X$; a subgradient oracle $f'$ on $X$), and moreover $\|f'(x)\|_* \le L_f$ for $x \in X$. Let $\psi$ be strongly convex on $X$ with parameter $\sigma > 0$, let $k \ge 1$, and let $(x^s)_{s \ge 1}$ be a SANP run whose step sizes satisfy, for $s = 1, \dots, k$,
--   $$t_s = \frac{\sqrt{2\sigma B_\psi(x^*, x^1)}}{L_f}\,\frac{1}{\sqrt k}. \tag{4.23}$$
--   Then
--   $$\min_{1 \le s \le k} f(x^s) - \min_{x \in X} f(x) \le L_f \sqrt{\frac{2 B_\psi(x^*, x^1)}{\sigma}}\,\frac{1}{\sqrt k}. \tag{4.24}$$
--
--   This is the efficiency estimate of SANP (and hence of mirror descent) with the optimal constant step for a horizon of $k$ iterations.
--
--   **Formalization Note** The step (4.23) is constant over the horizon $s = 1, \dots, k$: this is what the proof (minimising (4.25) over $t_1, \dots, t_k$) produces. An anytime schedule $t_s \propto 1/\sqrt s$ is not what is proved and would lose a $\log k$ factor. The bound $\|f'(x)\|_* \le L_f$ on the oracle is an added hypothesis: the proof uses it to pass from (4.22) to (4.25), and the Lipschitz condition of Assumption A does not imply it for subgradients relative to $X$ at boundary points. If $B_\psi(x^*, x^1) = 0$, the step (4.23) is $0$ and no SANP run exists, so that case is vacuous (and then $x^1 = x^*$). The "min" is stated as "there is $s \in \{1,\dots,k\}$ with $f(x^s) - f(x^*) \le \dots$". The SANP run replaces "nonempty interior" and "$x^1 \in \operatorname{int} X$".
-- source:
--   Beck & Teboulle, Mirror descent and nonlinear projected subgradient methods for convex optimization, Oper. Res. Lett. 31 (2003), p. 172, Theorem 4.2, (4.23)–(4.25)

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

namespace BeckTeboulleMD.EMDA

/-- Theorem 4.2, p. 172: under Assumption A, with subgradients bounded by `L_f` in the dual norm and
the step size `t_s = √(2σ B_ψ(x*, x¹)) / (L_f √k)` for `s = 1, …, k` (4.23),
`min_{1≤s≤k} f(x^s) − min_X f ≤ L_f √(2 B_ψ(x*, x¹) / σ) / √k` (4.24). -/
theorem theorem_4_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : E → ℝ) (hf : ConvexOn ℝ X f)
    (Lf : ℝ) (hLf : 0 < Lf) (hLip : ∀ x ∈ X, ∀ y ∈ X, |f x - f y| ≤ Lf * ‖x - y‖)
    (xstar : E) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    (g : E → E →L[ℝ] ℝ) (hg : ∀ x ∈ X, ∀ y ∈ X, f x + g x (y - x) ≤ f y)
    (hgb : ∀ y ∈ X, ‖g y‖ ≤ Lf)
    (ψ : E → ℝ) (σ : ℝ) (hσ : 0 < σ) (hψ : StrongConvexOn X σ ψ)
    (t : ℕ → ℝ) (x : ℕ → E) (hrun : IsSANPRun X ψ g t x)
    (k : ℕ) (hk : 1 ≤ k)
    (hstep : ∀ s, 1 ≤ s → s ≤ k →
      t s = Real.sqrt (2 * σ * bregman ψ xstar (x 1)) / (Lf * Real.sqrt k)) :
    ∃ s ∈ Finset.Icc 1 k,
      f (x s) - f xstar ≤ Lf * Real.sqrt (2 * bregman ψ xstar (x 1) / σ) / Real.sqrt k := by sorry

end BeckTeboulleMD.EMDA
