-- Prove2me | Theorems.Thm_DbarRegularity_norm_iteratedFDeriv_succ_le_partials
-- name    : DbarRegularity.norm_iteratedFDeriv_succ_le_partials
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-13T15:09:32.039739+00:00
-- url     : https://prove2.me/theorems/62a26eee-952f-4176-abc6-060c0daefc14
-- title:
--   The higher derivatives of a map on the plane are controlled by those of its two partial derivatives
-- statement:
--   Write $z=s+it$ for $z\in\mathbb{C}$. Let $F$ be a real normed space, $j\in\mathbb{N}$, and let $\varphi:\mathbb{C}\to F$ be of class $C^{j+1}$ over $\mathbb{R}$, with partial derivatives $\varphi_s=\partial\varphi/\partial s$ and $\varphi_t=\partial\varphi/\partial t$. Then for every $z\in\mathbb{C}$
--   $$\|D^{j+1}\varphi(z)\|\le\|D^j\varphi_s(z)\|+\|D^j\varphi_t(z)\|,$$
--   where $D^j$ is the $j$-th real Fréchet derivative and $\|\cdot\|$ the operator norm of a continuous multilinear map.
--
--   **Formalization Note** $D^j$ is `iteratedFDeriv ℝ j`, $\varphi_s$ is `fun x => fderiv ℝ φ x 1`, $\varphi_t$ is `fun x => fderiv ℝ φ x Complex.I`, and $C^{j+1}$ is `ContDiff ℝ (j + 1) φ`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: Asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13(3) (1996) 337–379, estimate (49), p. 366

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Basic

namespace DbarRegularity

open scoped ContDiff

/-- The `(j+1)`-st derivative of a map on `ℂ` is bounded pointwise by the `j`-th derivatives of
its two partial derivatives `∂φ/∂s = Dφ(·) 1` and `∂φ/∂t = Dφ(·) i`. -/
theorem norm_iteratedFDeriv_succ_le_partials {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {φ : ℂ → F} (j : ℕ) (hφ : ContDiff ℝ (j + 1) φ) (z : ℂ) :
    ‖iteratedFDeriv ℝ (j + 1) φ z‖
      ≤ ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ φ x 1) z‖
        + ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ φ x Complex.I) z‖ := by sorry

end DbarRegularity
