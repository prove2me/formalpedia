-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow
-- name    : AutomorphicForm.CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/051c603f-5d91-53f9-9ba1-904a7a36381b
-- title:
--   Flat involution preserves archimedean test factors
-- statement:
--   Let $F$ be a number field and $\sigma$ a real number, and let $fa \colon \mathrm{GL}_2(F_\infty) \to \mathbb{C}$ be a function on the general linear group over the infinite adele ring of $F$ satisfying `IsArchTestFactor F fa`, that is: there is a function $\Phi$ on $2\times 2$ matrices with entries in the mixed space $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ of $F$ which is $C^\infty$ in the real sense (`ContDiff ℝ ⊤`) and satisfies $fa(g) = \Phi(\mathrm{archEntries}\,g)$ for every $g$, where $\mathrm{archEntries}\,g$ is the matrix of entries of $g$ transported through the ring isomorphism from the infinite adele ring to the mixed space; and $fa$ has compact support. The conclusion is that the function $$y \longmapsto \overline{fa(y^{-1})}\cdot \bigl\lVert \det(\mathrm{adelicArchGLIncl}\,y)\bigr\rVert^{-\sigma}$$ again satisfies `IsArchTestFactor F`. Here $\mathrm{adelicArchGLIncl}$ is the monoid homomorphism placing $y$ in the archimedean component of $\mathrm{GL}_2(\mathbb{A}_F)$ and the identity in the finite component, and $\lVert\cdot\rVert$ is the idele norm, defined as the distributive Haar character of the adele ring evaluated at the given unit and read as a real number; the real power $(-\sigma)$ is then coerced into $\mathbb{C}$.
--
--   The operation $fa \mapsto fa^\flat$, with $fa^\flat(y) = \overline{fa(y^{-1})}\lVert \det y\rVert^{-\sigma}$, is the archimedean component of the adjoint of right convolution by $fa$ with respect to the $\sigma$-weighted pairing on automorphic forms. This lemma supplies the archimedean half of [`AutomorphicForm.CuspidalSpectrum.isFactorizableTestFn_flat`](thm.html#AutomorphicForm.CuspidalSpectrum.isFactorizableTestFn_flat), which states that the flat involution preserves factorizable test functions on $\mathrm{GL}_2(\mathbb{A}_F)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
open scoped ComplexConjugate

theorem AutomorphicForm.CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow
    (F : Type) [Field F] [NumberField F] (σ : ℝ)
    (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa : IsArchTestFactor F fa) :
    IsArchTestFactor F (fun y : GL (Fin 2) (InfiniteAdeleRing F) => conj (fa y⁻¹) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F y)) ^ (-σ) : ℝ) : ℂ)) := by sorry
