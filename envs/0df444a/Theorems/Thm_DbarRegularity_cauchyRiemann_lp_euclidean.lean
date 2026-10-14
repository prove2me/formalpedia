-- Prove2me | Theorems.Thm_DbarRegularity_cauchyRiemann_lp_euclidean
-- name    : DbarRegularity.cauchyRiemann_lp_euclidean
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T23:41:33.69532+00:00
-- url     : https://prove2.me/theorems/b852ec69-c146-4783-a9b2-ed4355a9d844
-- title:
--   The L^p Cauchy–Riemann estimate for maps into ℂⁿ
-- statement:
--   Write $z=s+it$ for $z\in\mathbb{C}$, $\varphi_s=\partial\varphi/\partial s$, $\varphi_t=\partial\varphi/\partial t$ and $\bar\partial\varphi=\varphi_s+i\varphi_t$. For every $n\in\mathbb{N}$ and every real $p>1$ there is a constant $A\ge0$ such that every $\varphi:\mathbb{C}\to\mathbb{C}^n$ of class $C^1$ with compact support satisfies
--   $$\|\varphi_s\|_{L^p(\mathbb{C})}+\|\varphi_t\|_{L^p(\mathbb{C})}\le A\,\|\bar\partial\varphi\|_{L^p(\mathbb{C})},$$
--   where $\mathbb{C}^n$ carries the Euclidean norm. This is the $L^p$ estimate for the Cauchy–Riemann operator on $\mathbb{C}^n$-valued maps of the plane, in the setting of Abbas–Hofer § 4.2.
--
--   **Formalization Note** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`. $\varphi_s$ is `fderiv ℝ φ z 1`, $\varphi_t$ is `fderiv ℝ φ z Complex.I`, and $\bar\partial\varphi$ is `DbarRegularity.dbar φ` $=$ `fderiv ℝ φ z 1 + Complex.I • fderiv ℝ φ z Complex.I` (no factor $1/2$). `ContDiff ℝ 1 φ` is $C^1$ smoothness over $\mathbb{R}$. The norms are `eLpNorm _ (ENNReal.ofReal p) volume`, valued in $[0,\infty]$; the constant $A$ is in `ℝ≥0` and depends only on $n$ and $p$.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter III, § 1.3, Proposition 4, p. 60

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic

namespace DbarRegularity

open MeasureTheory Metric
open scoped ENNReal NNReal

/-- For `1 < p < ∞` and `n : ℕ` there is `A` such that every `C¹` map `φ : ℂ → ℂⁿ` with compact
support satisfies `‖φ_s‖_p + ‖φ_t‖_p ≤ A ‖∂̄φ‖_p`. -/
theorem cauchyRiemann_lp_euclidean (n : ℕ) (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0, ∀ φ : ℂ → EuclideanSpace ℂ (Fin n), ContDiff ℝ 1 φ → HasCompactSupport φ →
      eLpNorm (fun z => fderiv ℝ φ z 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun z => fderiv ℝ φ z Complex.I) (ENNReal.ofReal p) volume
        ≤ A * eLpNorm (dbar φ) (ENNReal.ofReal p) volume := by sorry

end DbarRegularity
