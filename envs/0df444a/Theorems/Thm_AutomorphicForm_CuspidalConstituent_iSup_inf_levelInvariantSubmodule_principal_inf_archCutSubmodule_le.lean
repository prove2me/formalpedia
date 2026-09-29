-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_iSup_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_le
-- name    : AutomorphicForm.CuspidalConstituent.iSup_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/87928f7f-50df-5c99-94b8-a8e0f1022eb5
-- title:
--   Level-and-type cut distributes over finite sums of cusp subrepresentations
-- statement:
--   Let $F$ be a number field and $D$ an arbitrary subset of $\mathrm{GL}_2$ of the adele ring of $F$. Consider the carrier data `productionPinsOf` attached to $D$ whose level family is $N \mapsto$ `principalLevel` $\sqcap$ `finiteAdelicGL2Subgroup`, i.e. the principal congruence subgroup of level $N$ intersected with the kernel of the archimedean projection, whose Hecke elements are the `heckeGen` at the finite places, whose central subgroup is all of the adelic unit group, whose measures are the adelic $\mathrm{GL}_2$ Haar measure for the Borel structure and the additive adelic Haar measure conditioned on `adelicBox`; let $\xi$ be a character of that central subgroup with values in $\mathbb{C}^\times$. Let $N$ be an ideal of $\mathcal{O}_F$, let `tys` be an archimedean type family (for each infinite place $w$ a finite list of finite-dimensional representations of `rowIsometrySubgroup₀` of $F_w$), and let $\mathcal{V}$ be a finite set of $\mathbb{C}$-submodules of the space of functions $\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$, each $V \in \mathcal{V}$ satisfying `IsCuspSubrep` for these pins and $\xi$: $V$ lies in the span of the continuous functions all of whose right translates are smooth cusp automorphic functions for the pins and $\xi$ and which lie in some archimedean type cut, and $V$ is stable under right translation by the finite-adelic subgroup, under right translation by the images of the local row-isometry subgroups at the infinite places, and under right convolution by factorizable test functions that are archimedean bi-finite. The conclusion is that the intersection of the join $\bigvee_{V \in \mathcal{V}} V$ with the submodule of functions invariant under right translation by the level subgroup $K(N) \cap \mathrm{GL}_2(\mathbb{A}_{F,f})$ and with the type cut `archCutSubmodule F tys` (the infimum over infinite places $w$ of the join of the type submodules attached to the representations `tys.rep w i`) is contained in the join over $V \in \mathcal{V}$ of the corresponding intersections $V \sqcap$ level invariants $\sqcap$ type cut.
--
--   This is the non-trivial inclusion expressing that cutting by a principal congruence level and by a finite family of archimedean types commutes with finite sums of cuspidal subrepresentations, the opposite inclusion being formal. It is used in the finite spectral expansion of isotypic cusp forms at principal level, [`AutomorphicForm.CuspidalConstituent.exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule`](thm.html#AutomorphicForm.CuspidalConstituent.exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule), where finitely many constituents with finite-dimensional cuts must yield a finite-dimensional cut of their sum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_iSup_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_le.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalConstituent.iSup_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_le
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (tys : AutomorphicForm.ArchTypeFamily F)
    (𝒱 : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)))
    (h𝒱 : ∀ V ∈ 𝒱, IsCuspSubrep F (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V) :
    (⨆ V ∈ 𝒱, V) ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys ≤
      ⨆ V ∈ 𝒱, (V ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys) := by sorry
