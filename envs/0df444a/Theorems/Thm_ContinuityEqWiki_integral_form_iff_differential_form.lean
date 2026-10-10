-- Prove2me | Theorems.Thm_ContinuityEqWiki_integral_form_iff_differential_form
-- name    : ContinuityEqWiki.integral_form_iff_differential_form
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:58.53518+00:00
-- url     : https://prove2.me/theorems/0961f461-1e3a-4ab5-9627-b54cfe155ec8
-- title:
--   Continuity equation: integral form $\iff$ differential form
-- statement:
--   Let $\rho:\mathbb R\times\mathbb R^3\to\mathbb R$ be the volume density of a quantity $q$, $\mathbf j:\mathbb R\times\mathbb R^3\to\mathbb R^3$ its flux, and $\sigma:\mathbb R\times\mathbb R^3\to\mathbb R$ its generation rate per unit volume per unit time. Assume $\rho$ and $\mathbf j$ are $C^1$ jointly in $(t,x)$ and $\sigma$ is continuous. Then the following are equivalent.
--
--   1. **Integral form.** For every box $V=\prod_i[a_i,b_i]$ with $a_i<b_i$ and every time $t$,
--   $$\frac{dq}{dt}+\oint_{\partial V}\mathbf j\cdot d\mathbf S=\Sigma,\qquad q(t)=\int_V\rho(t,x)\,dx,\quad \Sigma(t)=\int_V\sigma(t,x)\,dx .$$
--   2. **Differential form.** For every $t$ and $x$,
--   $$\frac{\partial\rho}{\partial t}+\nabla\cdot\mathbf j=\sigma .$$
--
--   This is the central statement of the source: any continuity equation can be expressed either in integral form, for finite regions, or in differential form, at points.
--
--   **Formalization Note** The source quantifies over all closed surfaces $S$ enclosing a volume $V$. Here $V$ ranges over non-degenerate axis-parallel boxes, the setting of Mathlib's divergence theorem. This weakens the hypothesis of the direction (1)$\Rightarrow$(2) and the conclusion of (2)$\Rightarrow$(1).
-- source:
--   Wikipedia, "Continuity equation", revision oldid=1378634825, https://en.wikipedia.org/w/index.php?title=Continuity_equation&oldid=1378634825, section "General equation", subsections "Integral form" and "Differential form"

import Mathlib
import Definitions.Def_ContinuityEqWiki_Defs

namespace ContinuityEqWiki

theorem integral_form_iff_differential_form
    (ρ : ℝ → Space → ℝ) (j : ℝ → Space → Space) (σ : ℝ → Space → ℝ)
    (hρ : ContDiff ℝ 1 (Function.uncurry ρ)) (hj : ContDiff ℝ 1 (Function.uncurry j))
    (hσ : Continuous (Function.uncurry σ)) :
    IntegralForm ρ j σ ↔ DifferentialForm ρ j σ := by sorry

end ContinuityEqWiki
