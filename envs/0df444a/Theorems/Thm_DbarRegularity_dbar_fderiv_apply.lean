-- Prove2me | Theorems.Thm_DbarRegularity_dbar_fderiv_apply
-- name    : DbarRegularity.dbar_fderiv_apply
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-13T15:12:35.631544+00:00
-- url     : https://prove2.me/theorems/07b528a7-be06-49a4-954e-02acbeba100b
-- title:
--   The Cauchy–Riemann operator commutes with directional derivatives
-- statement:
--   Let $E$ be a complex normed space and let $\varphi:\mathbb{C}\to E$ be of class $C^2$ over $\mathbb{R}$. Write $\bar\partial\varphi=\partial\varphi/\partial s+i\,\partial\varphi/\partial t$ for $z=s+it$ (without the factor $1/2$), and for $w\in\mathbb C$ write $\partial_w\psi(z)=D\psi(z)\,w$. Then
--   $$\bar\partial(\partial_w\varphi)=\partial_w(\bar\partial\varphi)\qquad\text{on }\mathbb C.$$
--
--   **Formalization Note** $\bar\partial$ is `DbarRegularity.dbar`, $\partial_w\varphi$ is `fun z => fderiv ℝ φ z w`, and $C^2$ is `ContDiff ℝ 2 φ`. The identity is an equality of functions $\mathbb C\to E$.
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

/-- The Cauchy–Riemann operator commutes with a fixed directional derivative on `C²` maps. -/
theorem dbar_fderiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {φ : ℂ → E}
    (hφ : ContDiff ℝ 2 φ) (w : ℂ) :
    dbar (fun z => fderiv ℝ φ z w) = fun z => fderiv ℝ (dbar φ) z w := by sorry

end DbarRegularity
