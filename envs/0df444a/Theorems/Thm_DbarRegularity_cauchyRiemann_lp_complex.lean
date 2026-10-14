-- Prove2me | Theorems.Thm_DbarRegularity_cauchyRiemann_lp_complex
-- name    : DbarRegularity.cauchyRiemann_lp_complex
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T23:36:48.199209+00:00
-- url     : https://prove2.me/theorems/f9b3d864-cf3a-4677-8fc9-8284ebe4a7a4
-- title:
--   The L^p Cauchy–Riemann estimate in complex coordinates
-- statement:
--   Write $z=s+it$ for $z\in\mathbb{C}$, $f_s=\partial f/\partial s$, $f_t=\partial f/\partial t$ and $\bar\partial f=f_s+i f_t$. For every real $p>1$ there is a constant $A\ge 0$ such that every complex-valued $f:\mathbb{C}\to\mathbb{C}$ of class $C^1$ with compact support satisfies
--   $$\|f_s\|_{L^p(\mathbb{C})}+\|f_t\|_{L^p(\mathbb{C})}\le A\,\|\bar\partial f\|_{L^p(\mathbb{C})},$$
--   with respect to Lebesgue measure on $\mathbb{C}$. This is Stein's $L^p$ estimate for the Cauchy–Riemann operator in the plane, stated on $\mathbb{C}$ itself rather than on $\mathbb{R}^2$, in the form used for maps defined on discs in $\mathbb{C}$.
--
--   **Formalization Note** $f_s$ is `fderiv ℝ f z 1`, $f_t$ is `fderiv ℝ f z Complex.I`, and $\bar\partial f$ is `DbarRegularity.dbar f` $=$ `fderiv ℝ f z 1 + Complex.I • fderiv ℝ f z Complex.I` (no factor $1/2$). `ContDiff ℝ 1 f` is $C^1$ smoothness over $\mathbb{R}$. The norms are `eLpNorm _ (ENNReal.ofReal p) volume`, valued in $[0,\infty]$; the constant $A$ is in `ℝ≥0` and depends only on $p$.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter III, § 1.3, Proposition 4, p. 60

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic

namespace DbarRegularity

open MeasureTheory Metric
open scoped ENNReal NNReal

/-- For `1 < p < ∞` there is `A` such that every complex-valued `C¹` map `f : ℂ → ℂ` with compact
support satisfies `‖f_s‖_p + ‖f_t‖_p ≤ A ‖∂̄f‖_p`, where `z = s + i t`, `f_s = fderiv ℝ f z 1` and
`f_t = fderiv ℝ f z i`. -/
theorem cauchyRiemann_lp_complex (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0, ∀ f : ℂ → ℂ, ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm (fun z => fderiv ℝ f z 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun z => fderiv ℝ f z Complex.I) (ENNReal.ofReal p) volume
        ≤ A * eLpNorm (dbar f) (ENNReal.ofReal p) volume := by sorry

end DbarRegularity
