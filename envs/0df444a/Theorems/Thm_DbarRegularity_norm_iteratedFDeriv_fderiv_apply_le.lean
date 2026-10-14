-- Prove2me | Theorems.Thm_DbarRegularity_norm_iteratedFDeriv_fderiv_apply_le
-- name    : DbarRegularity.norm_iteratedFDeriv_fderiv_apply_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-13T15:07:18.44684+00:00
-- url     : https://prove2.me/theorems/9054e9ad-1b13-434a-a346-02ad0b15fb70
-- title:
--   A bound for the higher derivatives of a directional derivative
-- statement:
--   Let $D$ and $F$ be real normed spaces, $j\in\mathbb{N}$, and let $g:D\to F$ be of class $C^{j+1}$. For a fixed direction $w\in D$ write $\partial_w g(x)=Dg(x)\,w$. Then for every $z\in D$
--   $$\|D^j(\partial_w g)(z)\|\le \|w\|\,\|D^{j+1}g(z)\|,$$
--   where $D^j$ is the $j$-th Fréchet derivative and $\|\cdot\|$ the operator norm of a continuous multilinear map. The statement controls the derivatives of a directional derivative by the next derivative of the map itself.
--
--   **Formalization Note** $D^j$ is `iteratedFDeriv ℝ j`, $\partial_w g$ is `fun x => fderiv ℝ g x w`, and $C^{j+1}$ is `ContDiff ℝ (j + 1) g`.
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

/-- The `j`-th derivative of a directional derivative `x ↦ Dg(x) w` is bounded by `‖w‖` times the
`(j+1)`-st derivative of `g`. -/
theorem norm_iteratedFDeriv_fderiv_apply_le {D F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup F] [NormedSpace ℝ F] {g : D → F} (j : ℕ)
    (hg : ContDiff ℝ (j + 1) g) (w z : D) :
    ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ g x w) z‖
      ≤ ‖w‖ * ‖iteratedFDeriv ℝ (j + 1) g z‖ := by sorry

end DbarRegularity
