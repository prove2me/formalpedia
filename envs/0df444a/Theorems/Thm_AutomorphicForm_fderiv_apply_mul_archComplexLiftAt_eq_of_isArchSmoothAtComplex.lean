-- Prove2me | Theorems.Thm_AutomorphicForm_fderiv_apply_mul_archComplexLiftAt_eq_of_isArchSmoothAtComplex
-- name    : AutomorphicForm.fderiv_apply_mul_archComplexLiftAt_eq_of_isArchSmoothAtComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/651a5340-22f4-5593-82d3-a35666f5a26c
-- title:
--   Entry-chart derivative at a complex place in invariant directions
-- statement:
--   Let $F$ be a number field and $w$ a complex infinite place of $F$, and let $\varphi\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a function on the adelic group `AdelicGL2 (𝓞 F) F`. Assume `IsArchSmoothAtComplex hw φ`, that is: for every $h$ the chart map $e\mapsto\varphi(h\cdot \mathtt{archComplexLiftAt}\,hw\,e)$, defined on matrices $e : \mathrm{Fin}\,2\to\mathrm{Fin}\,2\to\mathbb{C}$ by transporting an invertible $e$ into $\mathrm{GL}_2$ of the completion at $w$ through the isomorphism of $F_w$ with $\mathbb{C}$ and including it adelically (and sending singular $e$ to $1$), is $C^\infty$ over $\mathbb{R}$ on $\{e \mid \det e \neq 0\}$. Fix $g\in\mathrm{GL}_2(\mathbb{A}_F)$, a matrix $e$ with $\det e\neq 0$, and an arbitrary complex $2\times 2$ matrix $Y$ as tangent vector. Put $A = e^{-1}Y$. Then the real Fréchet derivative of the chart $e'\mapsto \varphi(g\cdot\mathtt{archComplexLiftAt}\,hw\,e')$ at $e$, evaluated at $Y$, equals $\operatorname{Re}\alpha\,\partial_H\varphi+\operatorname{Im}\alpha\,\partial_{iH}\varphi+\operatorname{Re}A_{01}\,\partial_E\varphi+\operatorname{Im}A_{01}\,\partial_{iE}\varphi+\operatorname{Re}A_{10}\,\partial_{F^-}\varphi+\operatorname{Im}A_{10}\,\partial_{iF^-}\varphi$, with $\alpha=(A_{00}-A_{11})/2$, all six terms evaluated at $g\cdot\mathtt{archComplexLiftAt}\,hw\,e$, where $\partial_d\varphi(h)$ is `archDerivAtComplex`, the derivative at $t=0$ of $t\mapsto\varphi(h\cdot\mathtt{archComplexGLAt}\,hw\,(\mathtt{archFlowMatrixComplex}\,d\,t))$ for the six directions `H`, `E`, `Fm`, `iH`, `iE`, `iFm`; plus two central terms, $\operatorname{Re}\delta$ times the derivative at $0$ of $s\mapsto\varphi$ of $g\cdot\mathtt{archComplexLiftAt}\,hw\,e$ right-translated by the scalar matrix $\exp(s)$ placed at $w$, and $\operatorname{Im}\delta$ times the same with $\exp(is)$, where $\delta=(A_{00}+A_{11})/2$.
--
--   This is the chart-transport identity at a complex place: the real tangent space of $\mathrm{GL}_2(\mathbb{C})$ at $e$ is $e\cdot\mathfrak{gl}_2(\mathbb{C})$, eight-dimensional over $\mathbb{R}$, and every entry-coordinate real derivative of an archimedean-smooth adelic function is expressed through the six invariant derivatives in the directions $H,E,F^-,iH,iE,iF^-$ together with the two derivatives along the archimedean centre at $w$. It is used in [`AutomorphicForm.hasDerivAt_apply_mul_archComplexGLAt_inv_mul_archFlowMatrixComplex_mul`](thm.html#AutomorphicForm.hasDerivAt_apply_mul_archComplexGLAt_inv_mul_archFlowMatrixComplex_mul), in the development of the invariant differential operators (and ultimately the Casimir element) at a complex place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_fderiv_apply_mul_archComplexLiftAt_eq_of_isArchSmoothAtComplex.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace AutomorphicForm Complex

theorem AutomorphicForm.fderiv_apply_mul_archComplexLiftAt_eq_of_isArchSmoothAtComplex
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (g : AdelicGL2 (𝓞 F) F) (e : Fin 2 → Fin 2 → ℂ) (he : (Matrix.of e).det ≠ 0) (Y : Fin 2 → Fin 2 → ℂ) :
    fderiv ℝ (fun e' : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e')) e Y =
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 - ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2).re *
          archDerivAtComplex hw ArchDirComplex.H φ (g * archComplexLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 - ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2).im *
          archDerivAtComplex hw ArchDirComplex.iH φ (g * archComplexLiftAt hw e) +
      (((Matrix.of e)⁻¹ * Matrix.of Y) 0 1).re * archDerivAtComplex hw ArchDirComplex.E φ (g * archComplexLiftAt hw e) +
      (((Matrix.of e)⁻¹ * Matrix.of Y) 0 1).im * archDerivAtComplex hw ArchDirComplex.iE φ (g * archComplexLiftAt hw e) +
      (((Matrix.of e)⁻¹ * Matrix.of Y) 1 0).re * archDerivAtComplex hw ArchDirComplex.Fm φ (g * archComplexLiftAt hw e) +
      (((Matrix.of e)⁻¹ * Matrix.of Y) 1 0).im * archDerivAtComplex hw ArchDirComplex.iFm φ (g * archComplexLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 + ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2).re *
          deriv (fun s : ℝ => φ (g * archComplexLiftAt hw e *
            archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom
              (Units.mk0 (Complex.exp (s : ℂ)) (Complex.exp_ne_zero _))))) 0 +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 + ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2).im *
          deriv (fun s : ℝ => φ (g * archComplexLiftAt hw e *
            archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom
              (Units.mk0 (Complex.exp ((s : ℂ) * I)) (Complex.exp_ne_zero _))))) 0 := by sorry
