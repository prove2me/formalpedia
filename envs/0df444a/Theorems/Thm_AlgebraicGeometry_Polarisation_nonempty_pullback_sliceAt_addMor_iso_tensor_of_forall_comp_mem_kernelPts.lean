-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_sliceAt_addMor_iso_tensor_of_forall_comp_mem_kernelPts
-- name    : AlgebraicGeometry.Polarisation.nonempty_pullback_sliceAt_addMor_iso_tensor_of_forall_comp_mem_kernelPts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/0db9de70-13aa-510b-82d1-d9b8418c0400
-- title:
--   See-saw splitting of μ^*L on A ×_k Y
-- statement:
--   Let $k$ be an algebraically closed field, let $f : A \to \operatorname{Spec} k$ be a morphism of schemes equipped with a relative group law $L$ (a functorial group structure `mul`, `one`, `inv` on the sets of sections $\mathrm{SchemeHomOver}\,t\,f$ for all $t : T \to \operatorname{Spec} k$, with associativity, unit and inverse laws and compatibility with base change), and assume the bundle of properties `AbelianSchemePropertyBundle k f`: $f$ is smooth and proper, each set-theoretic fibre of $f$ is connected, and a relative group law on $f$ exists. Let $fY : Y \to \operatorname{Spec} k$ satisfy the same bundle of properties and let $j : Y \to A$ be a closed immersion with $j$ followed by $f$ equal to $fY$. Let $\mathcal L$ be an $\mathcal O_A$-module which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ with $\mathcal L|_U$ isomorphic to the unit module. Assume that for every section $y$ of $fY$ over $\operatorname{Spec} k$ the section $y$ followed by $j$ lies in $\mathrm{kernelPts}\,f\,L\,\mathcal L$, i.e. translation by that point leaves $\mathcal L$ locally unchanged (the pullback of $\mathcal L$ along right translation by the point is locally isomorphic, over the second projection, to the pullback of $\mathcal L$ along the first projection). Then the type of isomorphisms of modules on $A \times_{\operatorname{Spec} k} Y$ between the pullback of $\mathcal L$ along $\mathrm{sliceAt}\,f\,\langle j\rangle$ followed by $\mathrm{addMor}\,f\,L$ — the morphism $(a,y) \mapsto a + j(y)$ — and $p_1^*\mathcal L \otimes p_2^*\,j^*\mathcal L$ is nonempty.
--
--   This is the standard consequence of the see-saw principle and rigidity that a line bundle on an abelian variety becomes a "bi-additive-free" product when translated along a subvariety contained in $K(\mathcal L)$, as in Mumford's discussion of the kernel of the polarisation attached to $\mathcal L$. It feeds the computation of the Čech-theoretic rank attached to $\mathcal L$ in `cechFinrank_eq_zero_of_forall_comp_mem_kernelPts_of_not_nonempty_pullback_iso_unit`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_sliceAt_addMor_iso_tensor_of_forall_comp_mem_kernelPts.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_pullback_sliceAt_addMor_iso_tensor_of_forall_comp_mem_kernelPts
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    {Y : Scheme.{0}} (fY : Y ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ A) [IsClosedImmersion j] (hjf : j ≫ f = fY)
    (hY : AbelianSchemePropertyBundle k fY)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hstab : ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fY,
      (⟨y.1 ≫ j, by rw [Category.assoc, hjf, y.2]⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) ∈ kernelPts f L 𝓛) :
    Nonempty ((Scheme.Modules.pullback (sliceAt f (⟨j, hjf⟩ : SchemeHomOver fY f) ≫ addMor f L)).obj 𝓛 ≅
      (Scheme.Modules.pullback (pullback.fst f fY)).obj 𝓛 ⊗
        (Scheme.Modules.pullback (pullback.snd f fY)).obj ((Scheme.Modules.pullback j).obj 𝓛)) := by sorry
