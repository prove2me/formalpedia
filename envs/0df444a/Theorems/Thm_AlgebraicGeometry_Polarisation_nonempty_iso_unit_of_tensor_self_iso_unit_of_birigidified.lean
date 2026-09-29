-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_iso_unit_of_tensor_self_iso_unit_of_birigidified
-- name    : AlgebraicGeometry.Polarisation.nonempty_iso_unit_of_tensor_self_iso_unit_of_birigidified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/317edc43-5d35-57d4-873d-af85507a0b53
-- title:
--   A birigidified line bundle on A× A with trivial square is trivial
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a morphism, equipped with a relative group law $L$ on the functor of points of $f$ (functorial multiplication, unit, inverse and associativity, unit and inverse laws, together with naturality in the base) that is commutative, i.e. $L.\mathrm{mul}$ is symmetric on $T$-points for every $T$ over $\operatorname{Spec} k$. Assume the bundle of properties `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and a relative group law on $f$ exists. Let $g : \mathbb{N}$ be such that every fibre $f^{-1}(s)$ has topological Krull dimension $g$. Let $\mathcal{Q}$ be a module on the fibre product $A \times_{\operatorname{Spec} k} A$ which is invertible in the sense that every point has an open neighbourhood $U$ over which the restriction of $\mathcal{Q}$ is isomorphic to the unit sheaf of $U$. Write $e$ for the zero element of the additive group $L.\mathrm{AlgPoints}$ of $k$-points, that is the neutral point of the group law, and let $\mathrm{sliceAt}$ denote the closed immersion-type morphism $(\mathrm{fst}, \mathrm{snd} \circ e)$ from $A \times_{\operatorname{Spec} k} \operatorname{Spec} k$ into $A \times_{\operatorname{Spec} k} A$, so that pulling back along it restricts a module to the slice $A \times \{e\}$. Assume that the restriction of $\mathcal{Q}$ to this slice is isomorphic to the unit object, that the restriction of the pullback of $\mathcal{Q}$ along the symmetry isomorphism of $A \times_{\operatorname{Spec} k} A$ to this slice is likewise isomorphic to the unit object, and that $\mathcal{Q} \otimes \mathcal{Q}$ is isomorphic to the unit object. Then $\mathcal{Q}$ is isomorphic to the unit object of the monoidal category of modules on $A \times_{\operatorname{Spec} k} A$.
--
--   This is the $2$-torsion case of the assertion that the group of divisorial correspondences on $A \times A$, equivalently $\operatorname{Hom}(A,\hat A)$, is torsion-free: a birigidified invertible sheaf on $A \times A$ whose square is trivial is itself trivial. It is used in the construction of Mumford bundles attached to polarisations and in the verification of Rosati compatibility.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_iso_unit_of_tensor_self_iso_unit_of_birigidified.lean

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

theorem AlgebraicGeometry.Polarisation.nonempty_iso_unit_of_tensor_self_iso_unit_of_birigidified
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (𝓠 : (pullback f f).Modules) (h𝓠 : Scheme.Modules.IsInvertible 𝓠)
    (h₁ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj 𝓠 ≅ 𝟙_ _))
    (h₂ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓠) ≅ 𝟙_ _))
    (hsq : Nonempty (𝓠 ⊗ 𝓠 ≅ 𝟙_ _)) :
    Nonempty (𝓠 ≅ 𝟙_ (pullback f f).Modules) := by sorry
