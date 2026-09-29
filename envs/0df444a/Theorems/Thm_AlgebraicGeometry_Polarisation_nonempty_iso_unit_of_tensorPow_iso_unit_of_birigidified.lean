-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_iso_unit_of_tensorPow_iso_unit_of_birigidified
-- name    : AlgebraicGeometry.Polarisation.nonempty_iso_unit_of_tensorPow_iso_unit_of_birigidified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/014b12a6-118a-5ad7-b5c7-3d583d139588
-- title:
--   Bi-rigidified bundle with trivial n-th tensor power is trivial
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme, and $f : A \to \operatorname{Spec} k$ a morphism, equipped with a relative group law $L$ on $f$ — that is, functorial multiplication, unit and inverse operations on the $T$-points of $f$ over $\operatorname{Spec} k$ satisfying associativity, the two unit laws, left inversion and naturality under base change along $T' \to T$ — which is assumed commutative ($hc$). Assume further that $f$ satisfies the abelian-scheme property bundle: $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law; and that for some $g \in \mathbb{N}$ each fibre $f^{-1}(s)$ has topological Krull dimension $g$. Let $n > 0$, and let $\mathcal{Q}$ be a module on $A \times_{\operatorname{Spec} k} A$ which is invertible, in the sense that each point has an open neighbourhood $U$ over which the restriction of $\mathcal{Q}$ along $U \hookrightarrow A \times_{\operatorname{Spec} k} A$ is isomorphic to the unit sheaf of modules. Assume that the pullback of $\mathcal{Q}$ along the slice morphism determined by the zero element of the additive group of $k$-points of $L$ is isomorphic to the unit object, and likewise for the pullback of $\mathcal{Q}$ first along the symmetry isomorphism interchanging the two factors and then along that slice morphism; and that the $n$-fold tensor power of $\mathcal{Q}$, formed by the recursion $\mathcal{Q}^{\otimes 0} = \mathbf{1}$, $\mathcal{Q}^{\otimes (m+1)} = \mathcal{Q}^{\otimes m} \otimes \mathcal{Q}$, is isomorphic to the unit object. Then $\mathcal{Q}$ itself is isomorphic to the unit object of the monoidal category of modules on $A \times_{\operatorname{Spec} k} A$. All isomorphism assertions are asserted as nonemptiness of the corresponding type of isomorphisms.
--
--   This is the cancellation statement that a line bundle on $A \times_k A$ rigidified along $A \times \{e\}$ and $\{e\} \times A$ is trivial as soon as some positive tensor power of it is, proved via the biadditivity of the slices of such a bundle together with divisibility of $A(k)$ for $k$ algebraically closed. It underlies the special case $n = 2$, the compatibility of Rosati involutions with line bundles in $\operatorname{Pic}^0$, and the comparison of symmetry pullbacks with the Mumford bundle used to construct Riemann forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_iso_unit_of_tensorPow_iso_unit_of_birigidified.lean

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

theorem AlgebraicGeometry.Polarisation.nonempty_iso_unit_of_tensorPow_iso_unit_of_birigidified
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (n : ℕ) (hn : 0 < n)
    (𝓠 : (pullback f f).Modules) (h𝓠 : Scheme.Modules.IsInvertible 𝓠)
    (h₁ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj 𝓠 ≅ 𝟙_ _))
    (h₂ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓠) ≅ 𝟙_ _))
    (hpow : Nonempty (𝓠.tensorPow n ≅ 𝟙_ _)) :
    Nonempty (𝓠 ≅ 𝟙_ (pullback f f).Modules) := by sorry
