-- Prove2me | Theorems.Thm_AutomorphicForm_hasDerivAt_apply_mul_archRealGLAt_inv_mul_archFlowMatrix_mul
-- name    : AutomorphicForm.hasDerivAt_apply_mul_archRealGLAt_inv_mul_archFlowMatrix_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/f255d99e-cc58-5208-a940-4fb394042a58
-- title:
--   Directional derivative along a conjugated one-parameter subgroup
-- statement:
--   Let $K$ be a number field, $w$ a real infinite place of $K$ (hypothesis `hw : w.IsReal`), and let $G$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $K$ which satisfies `IsArchSmoothAt hw`, i.e. for every adelic $g$ the function $e \mapsto G(g \cdot \mathrm{archRealLiftAt}\,e)$ of a real $2\times 2$ entry matrix $e$ is $C^\infty$ on the open set where $\det e \neq 0$, where $\mathrm{archRealLiftAt}$ sends an invertible $e$ to its image in $\mathrm{GL}_2(\mathbb{A}_K)$ under the embedding $\mathrm{GL}_2(\mathbb{R}) \to \mathrm{GL}_2(\mathbb{A}_K)$ at $w$ furnished by the isomorphism $K_w \cong \mathbb{R}$ (and to $1$ otherwise). Let $y \in \mathrm{GL}_2(\mathbb{A}_K)$, let $m \in \mathrm{GL}_2(\mathbb{R})$, and let $d$ be one of the three directions $H$, $E$, $F^-$, with associated matrix $\mathrm{archDirMatrix}\,d$ equal to $\mathrm{diag}(1,-1)$, $\begin{pmatrix}0&1\\0&0\end{pmatrix}$, $\begin{pmatrix}0&0\\1&0\end{pmatrix}$ respectively, and one-parameter flow $\mathrm{archFlowMatrix}\,d\,s$ equal to $\mathrm{diag}(e^{s},e^{-s})$, the upper unipotent matrix with entry $s$, or the lower unipotent matrix with entry $s$. Put $Y = m^{-1}\,(\mathrm{archDirMatrix}\,d)\,m$ as a real matrix. Then the function $s \mapsto G\bigl(y \cdot \mathrm{archRealGLAt}\,hw\,(m^{-1}\,(\mathrm{archFlowMatrix}\,d\,s)\,m)\bigr)$ has derivative at $s = 0$ equal to $\frac{Y_{00}-Y_{11}}{2}\,(\mathrm{archDerivAt}\,H\,G)(y) + Y_{01}\,(\mathrm{archDerivAt}\,E\,G)(y) + Y_{10}\,(\mathrm{archDerivAt}\,F^-\,G)(y)$, the real coefficients being coerced into $\mathbb{C}$, where $\mathrm{archDerivAt}\,hw\,d\,G\,(g)$ is the derivative at $t=0$ of $t \mapsto G(g \cdot \mathrm{archRealGLAt}\,hw\,(\mathrm{archFlowMatrix}\,d\,t))$.
--
--   This is the elementary Lie-calculus computation expressing the derivative along a conjugated one-parameter subgroup $s \mapsto m^{-1}\exp(sX)m$ at a real place in terms of the three invariant derivations $H$, $E$, $F^-$ attached to that place. It is used in the regularity and chart-transport estimates for automorphic functions, being cited in the bounds for iterated derivatives along flow charts, in the boundedness statement for iterated `archDeriv` of right translates, and in the transport of archimedean character conditions under raising and lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_hasDerivAt_apply_mul_archRealGLAt_inv_mul_archFlowMatrix_mul.lean

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

theorem AutomorphicForm.hasDerivAt_apply_mul_archRealGLAt_inv_mul_archFlowMatrix_mul
    (K : Type) [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal)
    (G : AdelicGL2 (𝓞 K) K → ℂ) (hG : IsArchSmoothAt hw G) (y : AdelicGL2 (𝓞 K) K)
    (m : GL (Fin 2) ℝ) (d : ArchDir) :
    let Y : Matrix (Fin 2) (Fin 2) ℝ :=
      ((m⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d * (m : Matrix (Fin 2) (Fin 2) ℝ)
    HasDerivAt (fun s : ℝ => G (y * archRealGLAt hw (m⁻¹ * archFlowMatrix d s * m)))
      ((((Y 0 0 - Y 1 1) / 2 : ℝ) : ℂ) * archDerivAt hw ArchDir.H G y +
        ((Y 0 1 : ℝ) : ℂ) * archDerivAt hw ArchDir.E G y +
        ((Y 1 0 : ℝ) : ℂ) * archDerivAt hw ArchDir.Fm G y) 0 := by sorry
