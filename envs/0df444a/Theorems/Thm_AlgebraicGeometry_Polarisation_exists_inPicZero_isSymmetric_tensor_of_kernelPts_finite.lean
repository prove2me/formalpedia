-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_inPicZero_isSymmetric_tensor_of_kernelPts_finite
-- name    : AlgebraicGeometry.Polarisation.exists_inPicZero_isSymmetric_tensor_of_kernelPts_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/87fdaaee-8a49-5ce3-afb1-d8f74b59958e
-- title:
--   Symmetric Pic⁰-twist of a non-degenerate invertible sheaf
-- statement:
--   Let $k$ be an algebraically closed field, let $f : A \to \operatorname{Spec} k$ be a morphism of schemes, and let $L$ be a relative group law for $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-valued points over each $t : T \to \operatorname{Spec} k$, natural in $T$; assume $L$ is commutative, and assume the bundle of properties `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ carries a relative group law. Let $g$ be a natural number such that every fibre of $f$ has topological Krull dimension $g$. Let $\mathcal M$ be a module on $A$ which is invertible, i.e. locally on $A$ isomorphic to the unit sheaf, and suppose that the set of points $x$ of $A$ over $\operatorname{Spec} k$ lying in the stabiliser of $\mathcal M$ — those $x$ for which the pullback of $\mathcal M$ along right multiplication by $x$ is locally isomorphic, over the second projection, to the pullback of $\mathcal M$ along the first projection — is finite. Then there exists a module $Q$ on $A$ such that $Q$ is invertible and, for every point $x$ of $A$ over $\operatorname{Spec} k$, the pullback of $Q$ along translation by $x$ is isomorphic to $Q$ (this is `InPicZero`), and such that $\mathcal M \otimes Q$ is symmetric in the sense of `IsSymmetric`: for every point $s$ of $\operatorname{Spec} k$ there is an open neighbourhood $U$ of $s$ over which the pullback of $\mathcal M \otimes Q$ along the inversion morphism of $L$ and $\mathcal M \otimes Q$ itself become isomorphic after restriction to $f^{-1}(U)$.
--
--   This is the classical statement that an invertible sheaf with finite stabiliser scheme on an abelian variety over an algebraically closed field can be twisted by an element of $\mathrm{Pic}^0$ so as to become symmetric, the twist being $T_x^*\mathcal M \otimes \mathcal M^\vee$ for a suitable point $x$. It feeds the computation of the dimension of the space of sections of such a sheaf, via the results on $H^0$ of geometric fibres and on tensor powers that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_inPicZero_isSymmetric_tensor_of_kernelPts_finite.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_inPicZero_isSymmetric_tensor_of_kernelPts_finite
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (hK : (kernelPts f L 𝓜).Finite) :
    ∃ Q : A.Modules, InPicZero f L Q ∧ IsSymmetric f L (𝓜 ⊗ Q) := by sorry
