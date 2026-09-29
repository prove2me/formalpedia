-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_subset_iSupIndep_iSup_eq_of_finset_isCuspConstituent
-- name    : AutomorphicForm.CuspidalConstituent.exists_subset_iSupIndep_iSup_eq_of_finset_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/7ec28ca9-d30c-5f35-b6dc-f0baa551d629
-- title:
--   Independent subfamily with the same sum of cuspidal constituents
-- statement:
--   Let $F$ be a number field, let `pins` be a choice of carrier data for $F$ (a measurable space and measure on $\mathrm{GL}_2$ of the adele ring of $\mathcal{O}_F$, a fundamental-domain set $D$, a subgroup $Z$ of the ideles, a family of level subgroups indexed by ideals, local generators indexed by the finite places, and a measurable space and measure on the adele ring), and let $\xi : Z \to \mathbb{C}^{\times}$ be a group homomorphism. Let $\mathcal{V}$ be a finite set of $\mathbb{C}$-submodules of the space of functions $\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$, and assume every $V \in \mathcal{V}$ satisfies `IsCuspConstituent F pins ξ V`, i.e. $V$ is contained in the $K$-finite cuspidal submodule attached to $(F,\mathrm{pins},\xi)$, is stable under right translation by the elements of the finite-adelic $\mathrm{GL}_2$ subgroup and by the images of the row-isometry subgroups at each infinite place, is stable under right convolution by every factorizable test function that is archimedean-bi-finite for some archimedean type family, is non-zero, and is minimal among such stable submodules in the sense that any submodule $W$ with these stability properties and $W \le V$ is either $\bot$ or $V$. The conclusion is that there exists a finite subset $\mathcal{W} \subseteq \mathcal{V}$ such that the family of members of $\mathcal{W}$, indexed by $\mathcal{W}$ itself, is independent in the supremum lattice of submodules, and $\bigsqcup_{W \in \mathcal{W}} W = \bigsqcup_{V \in \mathcal{V}} V$.
--
--   This is the standard fact that a finite sum of simple (here: irreducible cuspidal) subrepresentations can be trimmed to a direct sum with the same total space, in the form needed for the cuspidal constituents of the adelic $\mathrm{GL}_2$ representation. It is used in the Langlands–Tunnell part of the development, where an isotypic cusp form is decomposed so that some single constituent carries a prescribed non-zero component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_subset_iSupIndep_iSup_eq_of_finset_isCuspConstituent.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_subset_iSupIndep_iSup_eq_of_finset_isCuspConstituent
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (𝒱 : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)))
    (h𝒱 : ∀ V ∈ 𝒱, IsCuspConstituent F pins ξ V) :
    ∃ 𝒲 : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)), 𝒲 ⊆ 𝒱 ∧
      iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))) ∧
      (⨆ W ∈ 𝒲, W) = ⨆ V ∈ 𝒱, V := by sorry
