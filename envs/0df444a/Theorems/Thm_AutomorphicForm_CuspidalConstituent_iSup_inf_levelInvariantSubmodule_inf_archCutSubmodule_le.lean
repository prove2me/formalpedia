-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_iSup_inf_levelInvariantSubmodule_inf_archCutSubmodule_le
-- name    : AutomorphicForm.CuspidalConstituent.iSup_inf_levelInvariantSubmodule_inf_archCutSubmodule_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/ac71ca32-7f5b-5bb6-b623-9a268aa513e2
-- title:
--   Level-and-type cut distributes over finite sums of cusp subrepresentations
-- statement:
--   Let $F$ be a number field, and let $D$ be a set in $\mathrm{GL}_2$ of the adeles of $F$. Write $\mathrm{pins}$ for the carrier data `productionPinsOf F D …` built from $D$ with the Borel $\sigma$-algebra and Haar measure on $\mathrm{GL}_2$ of the adeles, central subgroup $\top$, level family $N \mapsto$ `levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F` (the level-$N$ congruence subgroup intersected with the kernel of the archimedean projection), Hecke generators $v \mapsto$ `heckeGen (𝓞 F) F v` at the finite places, and the additive adelic Haar measure conditioned on `adelicBox F`. Let $\xi$ be a homomorphism from $\mathrm{pins}.Z$ to $\mathbb{C}^\times$, let $N$ be an ideal of $\mathcal{O}_F$, let $\mathrm{tys}$ be an archimedean type family on $F$ (a cardinality function on infinite places together with, at each place $w$, finitely many representations of `rowIsometrySubgroup₀ w.Completion`), and let $\mathcal{V}$ be a finite set of $\mathbb{C}$-submodules of the space of functions from $\mathrm{GL}_2$ of the adeles to $\mathbb{C}$, each member $V$ of which satisfies `IsCuspSubrep`: $V$ lies in the span of the continuous functions all of whose right translates are smooth cuspidal automorphic with central character $\xi$ and which lie in some archimedean cut submodule, and $V$ is stable under right translation by elements of `finiteAdelicGL2Subgroup F`, under right translation by the images of the groups `rowIsometrySubgroup₀ w.Completion` at all infinite places $w$, and under right convolution by factorizable, archimedean bi-finite test functions. The conclusion is the inclusion of submodules
--   $$\Bigl(\bigsqcup_{V \in \mathcal{V}} V\Bigr) \cap L \cap A \ \le\ \bigsqcup_{V \in \mathcal{V}} \bigl(V \cap L \cap A\bigr),$$
--   where the suprema are taken in the lattice of $\mathbb{C}$-submodules, $L =$ `levelInvariantSubmodule F pins N` is the space of functions $\varphi$ with $\varphi(gu) = \varphi(g)$ for all $g$ and all $u$ in `levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F`, and $A =$ `archCutSubmodule F tys` is the intersection over infinite places $w$ of the sum of the type submodules attached to the representations $\mathrm{tys}.\mathrm{rep}\, w\, i$. The reverse inclusion is automatic, so the statement is exactly the nontrivial half of the corresponding equality.
--
--   This is the statement that the cut by a fixed level and a fixed finite family of archimedean types, being effected by an idempotent built from averaging over the compact level group and projecting onto the archimedean types, commutes with forming finite sums of cuspidal subrepresentations. It is used to pass from 'finitely many constituents, each with finite-dimensional cut' to finite-dimensionality of the cut of their sum, and is invoked in the eigen-decomposition of isotypic cusp spaces, in the class-sum growth estimates and in the Rankin–Selberg analytic input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_iSup_inf_levelInvariantSubmodule_inf_archCutSubmodule_le.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalConstituent.iSup_inf_levelInvariantSubmodule_inf_archCutSubmodule_le
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (tys : AutomorphicForm.ArchTypeFamily F)
    (𝒱 : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)))
    (h𝒱 : ∀ V ∈ 𝒱, IsCuspSubrep F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V) :
    (⨆ V ∈ 𝒱, V) ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys ≤
      ⨆ V ∈ 𝒱, (V ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys) := by sorry
