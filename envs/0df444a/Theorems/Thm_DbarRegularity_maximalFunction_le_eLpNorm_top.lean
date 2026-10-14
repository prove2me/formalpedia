-- Prove2me | Theorems.Thm_DbarRegularity_maximalFunction_le_eLpNorm_top
-- name    : DbarRegularity.maximalFunction_le_eLpNorm_top
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T22:32:44.98019+00:00
-- url     : https://prove2.me/theorems/e177d79d-9b0b-4318-9d45-e981f0daa940
-- title:
--   The Hardy–Littlewood maximal function is bounded pointwise by the L^∞ norm
-- statement:
--   Let $Mf$ be the Hardy–Littlewood maximal function of $f:\mathbb{R}^d\to\mathbb{C}$,
--   $$Mf(x)=\sup_{r>0}\frac{1}{|B(x,r)|}\int_{B(x,r)}|f(y)|\,dy\in[0,\infty],$$
--   where $B(x,r)$ is the open ball and $|\cdot|$ is Lebesgue measure. Then for every $x\in\mathbb{R}^d$,
--   $$Mf(x)\le\|f\|_{L^\infty(\mathbb{R}^d)}.$$
--
--   This is the $L^\infty$ endpoint of the Hardy–Littlewood maximal theorem: the maximal operator is bounded on $L^\infty$ with norm at most $1$, and the bound holds at every point, not only almost everywhere.
--
--   **Formalization Note.** `maximalFunction f` (from `Definitions.Def_DbarRegularity_Setting`) takes values in `ℝ≥0∞`, and $\|f\|_{L^\infty}$ is `eLpNorm f ⊤ volume`, the essential supremum of $|f|$ in $[0,\infty]$. No measurability is assumed on $f$; if $f\notin L^\infty$ the right side is $+\infty$.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 1.3, Theorem 1 (c), p. 5, case p = ∞

import Definitions.Def_DbarRegularity_Setting

namespace DbarRegularity

open MeasureTheory
open scoped ENNReal

/-- The Hardy–Littlewood maximal function is bounded at every point by the `L^∞` norm (essential
supremum) of `f`: `M f (x) ≤ ‖f‖_∞`. -/
theorem maximalFunction_le_eLpNorm_top (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (x : EuclideanSpace ℝ (Fin d)) :
    maximalFunction f x ≤ eLpNorm f ⊤ volume := by sorry

end DbarRegularity
