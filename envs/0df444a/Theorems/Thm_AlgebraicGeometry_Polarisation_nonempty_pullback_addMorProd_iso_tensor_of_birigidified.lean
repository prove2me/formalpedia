-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_addMorProd_iso_tensor_of_birigidified
-- name    : AlgebraicGeometry.Polarisation.nonempty_pullback_addMorProd_iso_tensor_of_birigidified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/819ef760-cec1-5d04-99ba-6566aea968cb
-- title:
--   Biadditivity of a birigidified invertible sheaf on A× A
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$, and let $L$ be a relative group law on $f$, i.e. a functorial group structure (multiplication, unit, inverse, with associativity, unit and inverse laws and compatibility with base change) on the sets of $T$-valued points $\{\varphi : T \to A \mid \varphi \circ f = t\}$ for $t : T \to \operatorname{Spec} k$; assume $L$ is commutative, and assume the bundle of properties `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, every fibre of $f$ is connected, and $f$ carries a relative group law. Let $g$ be a natural number such that every fibre of $f$ has topological Krull dimension $g$. Let $\mathcal P$ be a sheaf of modules on $A \times_k A$ which is invertible in the sense that every point has a neighbourhood $U$ with $\mathcal P|_U$ isomorphic to the unit module. Write $e$ for the point of $A$ attached to the zero element of the additive group of $k$-points of $L$, and $\sigma$ for the symmetry of $A \times_k A$. Assume that the restriction of $\mathcal P$ along the slice $a \mapsto (a,e)$ is isomorphic to the unit module, and likewise the restriction of $\sigma^{*}\mathcal P$ along that slice (that is, $\mathcal P$ is trivial along $A \times \{e\}$ and along $\{e\} \times A$). Then, on $(A \times_k A) \times_k A$, there exists an isomorphism of modules between the pullback of $\mathcal P$ along $((a,b),c) \mapsto (a+b,c)$, where the addition is `addMor f L`, and the tensor product of the pullbacks of $\mathcal P$ along $((a,b),c) \mapsto (a,c)$ and along $((a,b),c) \mapsto (b,c)$; the assertion is the nonemptiness of the type of such isomorphisms.
--
--   This is the biadditivity (in the first variable) of a line bundle on $A \times A$ that is rigidified along both axes, the standard consequence of the theorem of the cube used in the theory of the Mumford bundle and of polarisations. It is invoked in the project's treatment of symmetric bundles, of the restriction of $\mathcal P$ to the diagonal, and of the Rosati-compatibility criteria for endomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_addMorProd_iso_tensor_of_birigidified.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_pullback_addMorProd_iso_tensor_of_birigidified
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (𝓟 : (pullback f f).Modules) (h𝓟 : Scheme.Modules.IsInvertible 𝓟)
    (h₁ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj 𝓟 ≅ 𝟙_ _))
    (h₂ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓟) ≅ 𝟙_ _)) :
    Nonempty ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ addMor f L) (pullback.snd (pullback.fst f f ≫ f) f)
          (by rw [Category.assoc, addMor_over]; exact pullback.condition))).obj 𝓟 ≅
      (Scheme.Modules.pullback
        (pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.fst f f) (pullback.snd (pullback.fst f f ≫ f) f)
          (by rw [Category.assoc]; exact pullback.condition))).obj 𝓟 ⊗
      (Scheme.Modules.pullback
        (pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f) (pullback.snd (pullback.fst f f ≫ f) f)
          (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]; exact pullback.condition))).obj 𝓟) := by sorry
