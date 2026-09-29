-- Prove2me | Theorems.Thm_AutomorphicForm_contDiff_apply_unipotentGL2_mixedSpace_mul_of_isArchSmoothAt_rat
-- name    : AutomorphicForm.contDiff_apply_unipotentGL2_mixedSpace_mul_of_isArchSmoothAt_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/69487471-5af7-563a-b497-de6b399191e8
-- title:
--   C² regularity along the unipotent archimedean direction over ℚ
-- statement:
--   Let $\varphi : \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ be a function on the adelic general linear group `AdelicGL2 (𝓞 ℚ) ℚ`, i.e. on $\mathrm{GL}_2$ of the adele ring of $\mathbb{Q}$, and assume `IsArchSmoothAt` holds for $\varphi$ at the unique infinite place of $\mathbb{Q}$, which is real: that is, for every $g$ the function sending a $2\times 2$ real matrix $e$ to $\varphi(g \cdot \mathrm{archRealLiftAt}(e))$ is $C^\infty$ on the open set of $e$ with $\det e \neq 0$, where $\mathrm{archRealLiftAt}$ carries an invertible real matrix to the adelic point supported at that real place (and sends singular $e$ to $1$). Then for every $g \in \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ the function on the mixed space $\mathrm{mixedSpace}\ \mathbb{Q}$ (a finite-dimensional real vector space) given by
--   $$z \longmapsto \varphi\bigl(n(x_z)\, g\bigr), \qquad n(x) = \begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix},$$
--   where $x_z$ is the adele whose infinite component is the image of $z$ under the inverse of the ring equivalence `InfiniteAdeleRing.ringEquiv_mixedSpace ℚ` and whose finite component is $0$, is of class $C^{\,\mathrm{finrank}_{\mathbb{Q}}\mathbb{Q} + 1}$ over $\mathbb{R}$, that is $C^2$. Only finitely many derivatives are asserted, not smoothness.
--
--   This is the regularity input needed to differentiate an automorphic form twice along the archimedean unipotent direction, as required for Casimir-operator and Whittaker-expansion computations on $\mathrm{GL}_2$ over $\mathbb{Q}$. It is used in the Langlands–Tunnell stage, in the construction of a cuspidal constituent with non-vanishing Whittaker coefficient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_contDiff_apply_unipotentGL2_mixedSpace_mul_of_isArchSmoothAt_rat.lean

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm

open scoped Classical in

theorem AutomorphicForm.contDiff_apply_unipotentGL2_mixedSpace_mul_of_isArchSmoothAt_rat
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hsm : IsArchSmoothAt Rat.isReal_infinitePlace φ)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ContDiff ℝ (Module.finrank ℚ ℚ + 1) (fun z : mixedEmbedding.mixedSpace ℚ =>
      φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm z, 0) * g)) := by sorry
