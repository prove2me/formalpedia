-- Prove2me | Theorems.Thm_AutomorphicForm_IsKfSmooth_finite_smul_image_of_isCompact
-- name    : AutomorphicForm.IsKfSmooth.finite_smul_image_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/f2a65bb0-08a7-5b86-a3df-9f16144f780a
-- title:
--   Finitely many translates of a K_f-smooth function on a compact set
-- statement:
--   Let $F$ be a number field, and write $\mathrm{GL}_2(\mathbb{A}_F)$ for `AdelicGL2 (𝓞 F) F`, the general linear group of degree $2$ over the adele ring of $F$. Let $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be any function, and let $G_f :=$ `finiteAdelicGL2Subgroup F` be the kernel of the homomorphism `glArch`, i.e. of the map $\mathrm{GL}_2(\mathbb{A}_F) \to \mathrm{GL}_2(\mathbb{A}_{F,\infty})$ obtained by applying the projection of the adeles onto the infinite adeles entrywise. Assume `IsKfSmooth F φ`, that is: regarding $\varphi$ as an element of the type synonym `RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ` of functions $\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ with its translation action of $G_f$, the stabiliser of $\varphi$ in $G_f$ is an open subset of $G_f$. Let $K$ be a compact subset of $G_f$ (with its subspace topology). Then the image of $K$ under the map $k \mapsto k \bullet \varphi$, i.e. the set of translates of $\varphi$ by elements of $K$, is a finite subset of `RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ`.
--
--   This is the standard finiteness of the orbit of a smooth vector under a compact set in a locally profinite group, specialised to the right-translation action of the finite-adelic subgroup of $\mathrm{GL}_2$ on complex-valued functions. It is used when a $K_f$-smooth automorphic function is analysed through finitely many translates, for instance in the results on right convolution and on level-spherical lifts in the cuspidal spectrum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsKfSmooth_finite_smul_image_of_isCompact.lean

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField FLT.SmoothVectors

theorem AutomorphicForm.IsKfSmooth.finite_smul_image_of_isCompact
    {F : Type} [Field F] [NumberField F] {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsKfSmooth F φ) {K : Set ↥(finiteAdelicGL2Subgroup F)} (hK : IsCompact K) :
    Set.Finite ((· • (RightTranslationFn.mk φ :
      RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ)) '' K) := by sorry
