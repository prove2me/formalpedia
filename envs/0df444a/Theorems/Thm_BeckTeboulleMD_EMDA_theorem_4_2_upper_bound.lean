-- Prove2me | Theorems.Thm_BeckTeboulleMD_EMDA_theorem_4_2_upper_bound
-- name    : BeckTeboulleMD.EMDA.theorem_4_2_upper_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:54:08.945601+00:00
-- url     : https://prove2.me/theorems/4a61d336-e5d9-46c7-8333-92c2519c97ce
-- title:
--   Remark after Theorem 4.2, pp. 172–173 — B_ψ(x*,x¹) replaced by an upper bound c (e.g. γ[ψ,x¹]) in (4.23)–(4.24)
-- statement:
--   Since $B_\psi(x^*, x^1)$ depends on the unknown optimum $x^*$, the step size (4.23) cannot be computed. The paper remarks that it may be replaced by $\gamma[\psi, x^1] = \max_{x \in X} B_\psi(x, x^1)$ when this is finite. More generally, any upper bound works.
--
--   Under the hypotheses of Theorem 4.2 (Assumption A, $L_f > 0$, $\|f'(x)\|_* \le L_f$ on $X$, $\psi$ strongly convex on $X$ with parameter $\sigma > 0$, a SANP run $(x^s)_{s\ge1}$), let $c > 0$ with $B_\psi(x^*, x^1) \le c$, let $k \ge 1$, and let the step sizes be $t_s = \sqrt{2\sigma c}/(L_f\sqrt k)$ for $s = 1, \dots, k$. Then
--   $$\min_{1 \le s \le k} f(x^s) - \min_{x \in X} f(x) \le L_f \sqrt{\frac{2c}{\sigma}}\,\frac{1}{\sqrt k}.$$
--
--   With $c = \gamma[\psi, x^1]$ this is the computable version of Theorem 4.2; with $X = \Delta$, $\psi = \psi_e$, $x^1 = n^{-1}e$ and $c = \ln n$ it gives Theorem 5.1.
--
--   **Formalization Note** The page states the replacement for $c = \gamma[\psi, x^1]$; the statement here holds for every upper bound $c$ of $B_\psi(x^*, x^1)$, which includes $\gamma[\psi, x^1]$ and avoids a real supremum. The step is constant over the horizon $1, \dots, k$, the oracle bound $\|f'\|_* \le L_f$ is an added hypothesis (as in Theorem 4.2), and the "min" is stated as an existence over $s \in \{1, \dots, k\}$.
-- source:
--   Beck & Teboulle, Mirror descent and nonlinear projected subgradient methods for convex optimization, Oper. Res. Lett. 31 (2003), pp. 172–173, remark after Theorem 4.2 (γ[ψ, y] := max_{x∈X} B_ψ(x, y))

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

namespace BeckTeboulleMD.EMDA

/-- The remark after Theorem 4.2, pp. 172–173: in (4.23) and (4.24) the unknown `B_ψ(x*, x¹)` may be
replaced by any finite upper bound `c` of it (such as `γ[ψ, x¹] = max_{x∈X} B_ψ(x, x¹)`): with
`t_s = √(2σc) / (L_f √k)` for `s = 1, …, k`,
`min_{1≤s≤k} f(x^s) − min_X f ≤ L_f √(2c / σ) / √k`. -/
theorem theorem_4_2_upper_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : E → ℝ) (hf : ConvexOn ℝ X f)
    (Lf : ℝ) (hLf : 0 < Lf) (hLip : ∀ x ∈ X, ∀ y ∈ X, |f x - f y| ≤ Lf * ‖x - y‖)
    (xstar : E) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    (g : E → E →L[ℝ] ℝ) (hg : ∀ x ∈ X, ∀ y ∈ X, f x + g x (y - x) ≤ f y)
    (hgb : ∀ y ∈ X, ‖g y‖ ≤ Lf)
    (ψ : E → ℝ) (σ : ℝ) (hσ : 0 < σ) (hψ : StrongConvexOn X σ ψ)
    (t : ℕ → ℝ) (x : ℕ → E) (hrun : IsSANPRun X ψ g t x)
    (c : ℝ) (hc : 0 < c) (hBc : bregman ψ xstar (x 1) ≤ c)
    (k : ℕ) (hk : 1 ≤ k)
    (hstep : ∀ s, 1 ≤ s → s ≤ k → t s = Real.sqrt (2 * σ * c) / (Lf * Real.sqrt k)) :
    ∃ s ∈ Finset.Icc 1 k,
      f (x s) - f xstar ≤ Lf * Real.sqrt (2 * c / σ) / Real.sqrt k := by sorry

end BeckTeboulleMD.EMDA
