-- Prove2me | Theorems.Thm_ConvexOptAlg_MirrorDescent_theorem_4_2
-- name    : ConvexOptAlg.MirrorDescent.theorem_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:03:47.78066+00:00
-- url     : https://prove2.me/theorems/baba6629-87ed-4826-b488-873a94c42363
-- title:
--   Theorem 4.2, pp. 299–300 — mirror descent with η = (R/L)√(2ρ/t) satisfies f((1/t)Σ x_s) − f(x*) ≤ RL√(2/(ρt))
-- statement:
--   Let $\|\cdot\|$ be an arbitrary norm on a finite-dimensional real space, $\mathcal X$ a compact convex set, and $\Phi$ a mirror map on the convex open set $\mathcal D$ with $\mathcal X\subseteq\overline{\mathcal D}$ and $\mathcal X\cap\mathcal D\ne\emptyset$. Assume $\Phi$ is $\rho$-strongly convex on $\mathcal X\cap\mathcal D$ with respect to $\|\cdot\|$ ($\rho>0$). Let $f$ be convex on $\mathcal X$ with a minimizer $x^*\in\mathcal X$, and let $L>0$. Let $t\ge1$ and let $(x_s,y_s,g_s)$ be a run of mirror descent on $f$ for the steps $1,\dots,t$ whose subgradients satisfy $\|g_s\|_*\le L$, where $x_1\in\operatorname{argmin}_{\mathcal X\cap\mathcal D}\Phi$. Let $R>0$ satisfy $\Phi(x)-\Phi(x_1)\le R^2$ for every $x\in\mathcal X\cap\mathcal D$. If the step size is
--   $$\eta=\frac RL\sqrt{\frac{2\rho}{t}},$$
--   then
--   $$f\Big(\frac1t\sum_{s=1}^t x_s\Big)-f(x^*)\le RL\sqrt{\frac{2}{\rho t}}.$$
--
--   The rate depends on the geometry only through $R^2$ and $\rho$; for the simplex with the negative entropy as mirror map ($\rho=1$ for the $\ell_1$ norm, $R^2=\log n$) it is $L\sqrt{2\log n/t}$, almost independent of the dimension.
--
--   **Formalization Note** The book sets $R^2=\sup_{x\in\mathcal X\cap\mathcal D}\Phi(x)-\Phi(x_1)$; here $R^2$ may be any upper bound of that supremum (a stronger statement; the page's $R$ is the case of equality). $R>0$ excludes only the degenerate case $\mathcal X=\{x_1\}$; $L>0$, $\rho>0$ and $t\ge1$ make the step and the bound well defined. The page's "$f$ is $L$-Lipschitz" ($\|g\|_*\le L$ for every subgradient relative to $\mathcal X$) is assumed only for the subgradients the run uses: a weaker hypothesis, hence a stronger statement, and the form that is not vacuous. Convexity of $f$, compactness and convexity of $\mathcal X$ and the existence of $x^*$ are standing assumptions of the book.
-- source:
--   Bubeck, arXiv:1405.4980v2, Theorem 4.2, pp. 299–300 (setting: Ch. 4 preamble, p. 297; §4.1, p. 298; (4.2)–(4.3), p. 299)

import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorDescent_Defs

namespace ConvexOptAlg.MirrorDescent

/-- Bubeck, Theorem 4.2, pp. 299–300. Let `Φ` be a mirror map `ρ`-strongly convex on `X ∩ D`
w.r.t. `‖·‖`, let `R > 0` with `Φ(x) − Φ(x_1) ≤ R²` for all `x ∈ X ∩ D` (the page takes
`R² = sup_{x ∈ X ∩ D} Φ(x) − Φ(x_1)`; any upper bound is allowed here), and let `f` be convex on
`X` with minimizer `x* ∈ X`, and let `L > 0` bound the dual norms `‖g_s‖_*` of the subgradients the
run uses (the page's `L`-Lipschitz assumption). Then every run of mirror
descent for `t ≥ 1` steps with `η = (R/L)√(2ρ/t)` satisfies
`f((1/t) ∑_{s=1}^t x_s) − f(x*) ≤ RL√(2/(ρt))`. -/
theorem theorem_4_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ)
    (hset : IsMirrorSetting X D Φ Φ')
    (ρ : ℝ) (hρ : 0 < ρ) (hΦ : IsStronglyConvexMirror X D Φ Φ' ρ)
    (f : E → ℝ) (hf : ConvexOn ℝ X f) (L : ℝ) (hL0 : 0 < L)
    (xstar : E) (hxstar : xstar ∈ X) (hmin : ∀ z ∈ X, f xstar ≤ f z)
    (t : ℕ) (ht : 1 ≤ t) (x y : ℕ → E) (g : ℕ → E →L[ℝ] ℝ)
    (hgL : ∀ s : ℕ, 1 ≤ s → s ≤ t → ‖g s‖ ≤ L)
    (R : ℝ) (hR0 : 0 < R) (hR : ∀ z ∈ X ∩ D, Φ z - Φ (x 1) ≤ R ^ 2)
    (hrun : IsMirrorDescentRun X D Φ Φ' f (R / L * Real.sqrt (2 * ρ / t)) x y g t) :
    f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x s) - f xstar ≤
      R * L * Real.sqrt (2 / (ρ * t)) := by sorry

end ConvexOptAlg.MirrorDescent
