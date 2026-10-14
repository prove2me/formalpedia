-- Prove2me | Theorems.Thm_DbarRegularity_eLpNorm_iteratedFDeriv_succ_le_dbar
-- name    : DbarRegularity.eLpNorm_iteratedFDeriv_succ_le_dbar
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-13T15:24:46.739157+00:00
-- url     : https://prove2.me/theorems/2cccff0c-f5ea-4f33-92ba-780275b88cb7
-- title:
--   Higher-order L^p estimates for the Cauchy–Riemann operator on the plane
-- statement:
--   Write $z=s+it$ for $z\in\mathbb{C}$ and $\bar\partial\varphi=\partial\varphi/\partial s+i\,\partial\varphi/\partial t$ (without the factor $1/2$). Let $n\in\mathbb{N}$ and $p\in(1,\infty)$ real. There is a constant $A\ge0$ such that for every $j\in\mathbb N$ and every smooth compactly supported $\varphi:\mathbb{C}\to\mathbb{C}^n$,
--   $$\|D^{j+1}\varphi\|_{L^p(\mathbb{C})}\le 2^j A\,\|D^j(\bar\partial\varphi)\|_{L^p(\mathbb{C})},$$
--   where $D^j$ is the $j$-th real Fréchet derivative, measured pointwise in the operator norm of continuous multilinear maps, and $L^p$ is taken with respect to Lebesgue measure. The constant $A$ depends only on $n$ and $p$. This is the higher-order version of the $L^p$ estimate for $\bar\partial$ on the whole plane.
--
--   **Formalization Note** $\mathbb C^n$ is `EuclideanSpace ℂ (Fin n)`, $D^j$ is `iteratedFDeriv ℝ j`, $\bar\partial$ is `DbarRegularity.dbar`, smoothness is `ContDiff ℝ ∞ φ`, and compact support is `HasCompactSupport φ`. The norms are `eLpNorm _ (ENNReal.ofReal p) volume`, valued in $[0,\infty]$, and the constant is the coercion of `2 ^ j * A : ℝ≥0`. The single constant $A$ is chosen before $j$.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: Asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13(3) (1996) 337–379, estimate (49), p. 366

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic

namespace DbarRegularity

open MeasureTheory
open scoped ENNReal NNReal ContDiff

/-- Higher-order `L^p` estimate for the Cauchy–Riemann operator on the whole plane: for `1 < p`
there is `A` such that for every `j` and every smooth compactly supported `φ : ℂ → ℂⁿ`,
`‖D^{j+1} φ‖_{L^p} ≤ 2^j A ‖D^j (∂̄φ)‖_{L^p}`. -/
theorem eLpNorm_iteratedFDeriv_succ_le_dbar (n : ℕ) (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0, ∀ (j : ℕ) (φ : ℂ → EuclideanSpace ℂ (Fin n)), ContDiff ℝ ∞ φ →
      HasCompactSupport φ →
      eLpNorm (iteratedFDeriv ℝ (j + 1) φ) (ENNReal.ofReal p) volume
        ≤ ((2 ^ j * A : ℝ≥0) : ℝ≥0∞)
          * eLpNorm (iteratedFDeriv ℝ j (dbar φ)) (ENNReal.ofReal p) volume := by sorry

end DbarRegularity
