-- Prove2me | Theorems.Thm_AutomorphicForm_exists_archDerivAtComplex_Fm_sub_E_and_iE_add_iFm_eq_rightTranslate_iH_rightTranslate
-- name    : AutomorphicForm.exists_archDerivAtComplex_Fm_sub_E_and_iE_add_iFm_eq_rightTranslate_iH_rightTranslate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/fe437001-961a-5942-9547-4d905e034170
-- title:
--   Compact directions F-E and i(E+F) are iH-conjugates
-- statement:
--   Let $K$ be a number field and let $w$ be an infinite place of $K$ with $hw : w.\mathrm{IsComplex}$. The assertion is that there exist two elements $k_1, k_2$ of the subgroup `rowIsometrySubgroup₀` of $GL_2$ over the completion $K_w$ — chosen once and for all, independently of the function below — such that the following holds for every $\psi : GL_2(\mathbb{A}_K) \to \mathbb{C}$ (where $GL_2(\mathbb{A}_K)$ is `AdelicGL2 (𝓞 K) K`, the general linear group of degree $2$ over the adele ring) which is smooth at $w$ in the sense of `IsArchSmoothAtComplex hw`, i.e. for every $g$ the map sending a $2\times 2$ complex matrix $e$ to $\psi(g \cdot \text{archComplexLiftAt } hw\, e)$ is $C^\infty$ in the real sense on the open set of $e$ with $\det e \neq 0$. Writing $D_d\psi(g) = \frac{d}{dt}\psi\bigl(g\cdot \text{archComplexGLAt } hw\,(\text{archFlowMatrixComplex } d\, t)\bigr)\big|_{t=0}$ for the flow derivative in the direction $d \in \{H, E, F, iH, iE, iF\}$ at the place $w$, and $R_k\varphi = \varphi(\,\cdot\,k)$ for right translation, the two identities of functions on $GL_2(\mathbb{A}_K)$ hold: $D_{F}\psi - D_{E}\psi = R_{\iota(k_1)}\bigl(D_{iH}(R_{\iota(k_1^{-1})}\psi)\bigr)$ and $D_{iE}\psi + D_{iF}\psi = R_{\iota(k_2)}\bigl(D_{iH}(R_{\iota(k_2^{-1})}\psi)\bigr)$, where $\iota = \text{rowIsometryInclAt₀ } K\, w$ places an element of `rowIsometrySubgroup₀` at the place $w$ inside the adelic group.
--
--   This expresses the classical fact that the three compact directions $iH$, $F-E$ and $i(E+F)$ of $\mathfrak{su}(2) \subset \mathfrak{sl}_2(\mathbb{C})$ are conjugate inside the determinant-one row-isometry group at a complex place, transported to flow derivatives of functions on the adelic group by right translation. It is used in the estimate [`AutomorphicForm.exists_forall_eLpNorm_archDerivAtComplex_iH_and_E_sub_Fm_and_iE_add_iFm_foldr_le_of_mem_archCutSubmodule`](thm.html#AutomorphicForm.exists_forall_eLpNorm_archDerivAtComplex_iH_and_E_sub_Fm_and_iE_add_iFm_foldr_le_of_mem_archCutSubmodule), where bounds for the single direction $iH$ are thereby spread to the whole compact part of the Lie algebra at $w$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_archDerivAtComplex_Fm_sub_E_and_iE_add_iFm_eq_rightTranslate_iH_rightTranslate.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_archDerivAtComplex_Fm_sub_E_and_iE_add_iFm_eq_rightTranslate_iH_rightTranslate
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex) :
    ∃ k₁ k₂ : rowIsometrySubgroup₀ w.Completion,
      ∀ ψ : AdelicGL2 (𝓞 K) K → ℂ, IsArchSmoothAtComplex hw ψ →
        (archDerivAtComplex hw .Fm ψ - archDerivAtComplex hw .E ψ =
          rightTranslate K (rowIsometryInclAt₀ K w k₁)
            (archDerivAtComplex hw .iH (rightTranslate K (rowIsometryInclAt₀ K w k₁⁻¹) ψ))) ∧
        (archDerivAtComplex hw .iE ψ + archDerivAtComplex hw .iFm ψ =
          rightTranslate K (rowIsometryInclAt₀ K w k₂)
            (archDerivAtComplex hw .iH (rightTranslate K (rowIsometryInclAt₀ K w k₂⁻¹) ψ))) := by sorry
