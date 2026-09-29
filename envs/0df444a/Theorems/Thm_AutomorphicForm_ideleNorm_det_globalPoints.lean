-- Prove2me | Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
-- name    : AutomorphicForm.ideleNorm_det_globalPoints
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/6b3545f9-ee26-5783-b8c2-324aff291c8e
-- title:
--   Principal ideles have idele norm one, via det on GL₂
-- statement:
--   Let $F$ be a number field and let $\gamma$ be an element of the general linear group $GL_2(F)$ of $2\times 2$ matrices over $F$. Write $\mathbb{A}_F$ for the adele ring of $F$ (formed from the ring of integers $\mathcal{O}_F$ and $F$), and let $GL_2(\mathbb{A}_F)$ be the corresponding group of $2\times 2$ invertible adelic matrices. The monoid homomorphism [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15) sends $\gamma$ to its image under the entrywise map induced by the structure map $F \to \mathbb{A}_F$, so $\gamma$ is viewed as an adelic matrix through the diagonal embedding. Taking the determinant of that image gives a unit of $\mathbb{A}_F$, that is an idele. The assertion is that the real number [`NumberField.TateGlobal.ideleNorm F`](def/NumberField_TateGlobalZeta.html#L19) of this idele equals $1$, where the idele norm of an idele $x$ is by definition the value, pushed into $\mathbb{R}$ through $\mathbb{R}_{\ge 0}$, of the character `distribHaarChar` of $\mathbb{A}_F$ at $x$: the factor by which multiplication by $x$ scales an additive Haar measure on $\mathbb{A}_F$.
--
--   This is the product formula for a number field, in the form '$\|a\|_{\mathbb{A}} = 1$ for a principal idele $a$', packaged for the determinant on $GL_2$. It is what makes left translation by an element of $GL_2(F)$ preserve any condition imposed on $\|\det g\|_{\mathbb{A}}$, for instance a determinant slab $d_1 \le \|\det g\|_{\mathbb{A}} \le d_2$, and is used throughout the adelic integration and fundamental-domain arguments for automorphic forms on $GL_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ideleNorm_det_globalPoints.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped NumberField

theorem AutomorphicForm.ideleNorm_det_globalPoints
    {F : Type} [Field F] [NumberField F] (γ : Matrix.GeneralLinearGroup (Fin 2) F) :
    NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det (AutomorphicForm.globalPoints (𝓞 F) F γ)) = 1 := by sorry
