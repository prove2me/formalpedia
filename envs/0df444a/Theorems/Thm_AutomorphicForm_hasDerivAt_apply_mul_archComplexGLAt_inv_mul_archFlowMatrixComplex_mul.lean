-- Prove2me | Theorems.Thm_AutomorphicForm_hasDerivAt_apply_mul_archComplexGLAt_inv_mul_archFlowMatrixComplex_mul
-- name    : AutomorphicForm.hasDerivAt_apply_mul_archComplexGLAt_inv_mul_archFlowMatrixComplex_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/d408535b-cff6-5730-be7a-d9b87b21c01d
-- title:
--   Derivative along a conjugated one-parameter flow at a complex place
-- statement:
--   Let $K$ be a number field, $w$ an infinite place of $K$ with $hw$ a proof that $w$ is complex, and let $G$ be a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_K)$ (the units of $2\times 2$ matrices over the adele ring of $\mathcal{O}_K$ in $K$) satisfying `IsArchSmoothAtComplex hw`, that is: for every adelic $g$ the function $e \mapsto G(g\cdot\mathrm{archComplexLiftAt}\,hw\,e)$ on $2\times2$ complex matrices is $C^\infty$ over $\mathbb{R}$ on the open set where $\det e \neq 0$, where `archComplexLiftAt` sends an invertible $e$ to its image under the monoid map $\mathrm{archComplexGLAt}\,hw : \mathrm{GL}_2(\mathbb{C}) \to \mathrm{GL}_2(\mathbb{A}_K)$ obtained from the isomorphism $K_w \cong \mathbb{C}$ followed by the inclusion at $w$. Let $y$ be an adelic point, $m \in \mathrm{GL}_2(\mathbb{C})$, and $d$ one of the six directions $H, E, F^-, iH, iE, iF^-$, with associated matrix $X$ ($\mathrm{diag}(1,-1)$, $e_{01}$, $e_{10}$, and $i$ times each) and one-parameter flow $\mathrm{archFlowMatrixComplex}\,d\,s$ equal to $\mathrm{diag}(e^{s},e^{-s})$, the upper or lower unipotent with entry $s$, or the corresponding matrices with $s$ replaced by $is$. Put $Y = m^{-1}Xm$. Then $s \mapsto G\bigl(y\cdot \mathrm{archComplexGLAt}\,hw\,(m^{-1}\,\mathrm{archFlowMatrixComplex}\,d\,s\;m)\bigr)$ has derivative at $s=0$ equal to $\mathrm{Re}\frac{Y_{00}-Y_{11}}{2}\,(H G)(y) + \mathrm{Im}\frac{Y_{00}-Y_{11}}{2}\,(iH\,G)(y) + \mathrm{Re}\,Y_{01}\,(E G)(y) + \mathrm{Im}\,Y_{01}\,(iE\,G)(y) + \mathrm{Re}\,Y_{10}\,(F^- G)(y) + \mathrm{Im}\,Y_{10}\,(iF^-\,G)(y)$, the real coefficients being coerced into $\mathbb{C}$ and each $(\cdot\,G)(y)$ denoting $\mathrm{archDerivAtComplex}\,hw$ in that direction, i.e. the derivative at $t=0$ of $t\mapsto G(y\cdot\mathrm{archComplexGLAt}\,hw\,(\mathrm{archFlowMatrixComplex}\,\cdot\,t))$, evaluated at $y$.
--
--   This is the complex-place form of the statement that a directional derivative along a conjugated one-parameter subgroup $s\mapsto m^{-1}\exp(sX)m$ at a complex place decomposes in the basis of the six invariant derivations attached to $H, E, F^-, iH, iE, iF^-$. It is used in the chart-transport estimates for archimedean smoothness: the bounds on iterated derivatives along flow charts, the boundedness and smoothness of right translates by row-isometry inclusions, and the statement that right translates of iterated archimedean derivatives lie in the span of such iterated derivatives.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_hasDerivAt_apply_mul_archComplexGLAt_inv_mul_archFlowMatrixComplex_mul.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.InfinitePlace
open AutomorphicForm
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel
open scoped ComplexConjugate

theorem AutomorphicForm.hasDerivAt_apply_mul_archComplexGLAt_inv_mul_archFlowMatrixComplex_mul
    (K : Type) [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsComplex)
    (G : AdelicGL2 (𝓞 K) K → ℂ) (hG : IsArchSmoothAtComplex hw G) (y : AdelicGL2 (𝓞 K) K)
    (m : GL (Fin 2) ℂ) (d : ArchDirComplex) :
    let X : Matrix (Fin 2) (Fin 2) ℂ := match d with
      | .H => !![1, 0; 0, -1] | .E => !![0, 1; 0, 0] | .Fm => !![0, 0; 1, 0]
      | .iH => !![Complex.I, 0; 0, -Complex.I] | .iE => !![0, Complex.I; 0, 0] | .iFm => !![0, 0; Complex.I, 0]
    let Y : Matrix (Fin 2) (Fin 2) ℂ := ((m⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * X * (m : Matrix (Fin 2) (Fin 2) ℂ)
    HasDerivAt (fun s : ℝ => G (y * archComplexGLAt hw (m⁻¹ * archFlowMatrixComplex d s * m)))
      ((((Y 0 0 - Y 1 1) / 2).re : ℂ) * archDerivAtComplex hw ArchDirComplex.H G y +
        (((Y 0 0 - Y 1 1) / 2).im : ℂ) * archDerivAtComplex hw ArchDirComplex.iH G y +
        ((Y 0 1).re : ℂ) * archDerivAtComplex hw ArchDirComplex.E G y +
        ((Y 0 1).im : ℂ) * archDerivAtComplex hw ArchDirComplex.iE G y +
        ((Y 1 0).re : ℂ) * archDerivAtComplex hw ArchDirComplex.Fm G y +
        ((Y 1 0).im : ℂ) * archDerivAtComplex hw ArchDirComplex.iFm G y) 0 := by sorry
