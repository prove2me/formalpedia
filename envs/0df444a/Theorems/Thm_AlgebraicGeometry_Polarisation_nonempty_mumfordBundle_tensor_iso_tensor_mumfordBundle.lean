-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_tensor_iso_tensor_mumfordBundle
-- name    : AlgebraicGeometry.Polarisation.nonempty_mumfordBundle_tensor_iso_tensor_mumfordBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/5a3d07d3-d13a-5ccc-9e57-759da5f92bd9
-- title:
--   Multiplicativity of the Mumford bundle in the line bundle
-- statement:
--   Let $S$ be a commutative ring and let $f : A \to \operatorname{Spec} S$ be a morphism of schemes, equipped with a term $L$ of `RelativeGroupLaw S f`, i.e. a functorial group law on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-points over $\operatorname{Spec} S$ (multiplication, unit and inverse for each $t : T \to \operatorname{Spec} S$, associativity, unit laws, left inverse law, and compatibility with base change along $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$). Let $N, N'$ be objects of `A.Modules` that are invertible in the sense of `Scheme.Modules.IsInvertible`: every point of $A$ has an open neighbourhood $U$ over which the pullback along $U \hookrightarrow A$ is isomorphic to the unit module of the sheaf of rings of $U$. For an $\mathcal O_A$-module $\mathcal L$, `mumfordBundle f L` is the module $m^*\mathcal L \otimes (p_1^* \mathcal L^\vee \otimes p_2^* \mathcal L^\vee)$ on $A \times_{\operatorname{Spec} S} A$, where $p_1, p_2$ are the two projections, $m$ is the morphism `addMor f L` given by multiplying the two projections in the group law, and $\mathcal L^\vee$ is the internal hom from $\mathcal L$ to the monoidal unit. The assertion is that the type of isomorphisms $\Lambda(N \otimes N') \cong \Lambda(N) \otimes \Lambda(N')$ is nonempty, with $\Lambda =$ `mumfordBundle f L`.
--
--   This is the multiplicativity of Mumford's bundle $\Lambda(\mathcal L) = m^*\mathcal L \otimes p_1^*\mathcal L^\vee \otimes p_2^*\mathcal L^\vee$ on $A \times_S A$ in the line bundle variable, the sheaf-theoretic input behind the biadditivity properties of Mumford's construction. It is used in the treatment of polarisations and the Rosati involution, and in the construction of canonical polarisation data on fake elliptic curves over Artinian bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_tensor_iso_tensor_mumfordBundle.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_mumfordBundle_tensor_iso_tensor_mumfordBundle
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (N N' : A.Modules) (hN : Scheme.Modules.IsInvertible N) (hN' : Scheme.Modules.IsInvertible N') :
    Nonempty (mumfordBundle f L (N ⊗ N') ≅ mumfordBundle f L N ⊗ mumfordBundle f L N') := by sorry
