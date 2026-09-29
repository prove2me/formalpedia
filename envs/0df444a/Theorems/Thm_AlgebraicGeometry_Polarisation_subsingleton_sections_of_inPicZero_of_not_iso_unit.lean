-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_subsingleton_sections_of_inPicZero_of_not_iso_unit
-- name    : AlgebraicGeometry.Polarisation.subsingleton_sections_of_inPicZero_of_not_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/cad2b869-b896-5fe9-bec7-aed811960372
-- title:
--   Nontrivial line bundle in Pic⁰ has no sections
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law for $f$: that is, functorial multiplication, unit and inverse operations on the sets of $T$-points of $A$ over $\operatorname{Spec} k$, for every $k$-scheme $T$, satisfying associativity, the unit laws, left inverse cancellation and compatibility with base change along morphisms $T' \to T$ over $\operatorname{Spec} k$. Assume that $L$ is commutative, i.e. multiplication on $T$-points is commutative for every $T$, and that $f$ satisfies the abelian-scheme property bundle: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $M$ be a module over the structure sheaf of $A$ such that `InPicZero f L M` holds, namely (i) $M$ is invertible in the sense that every point of $A$ has an open neighbourhood $U$ over which the restriction of $M$ is isomorphic to the unit module of $U$, and (ii) for every $k$-point $x$ of $A$ (a section of $f$ over the identity of $\operatorname{Spec} k$) the pullback of $M$ along the translation morphism $L.\mathrm{translate}\,x : A \to A$ is isomorphic to $M$. Assume further that $M$ is not isomorphic to the monoidal unit of $A$-modules. Then the type $\Gamma(M, \top)$ of global sections of $M$ is a subsingleton, i.e. $\Gamma(A, M) = 0$.
--
--   This is the statement that a line bundle in $\operatorname{Pic}^0$ of an abelian variety over an algebraically closed field has no nonzero global sections unless it is trivial (Mumford, Abelian Varieties, §8). It feeds the vanishing and acyclicity results for $\operatorname{Pic}^0$-classes used in the construction of polarisations, being cited by the statements on $H^0$ and the higher cohomology of such bundles, on the existence of a class in $\operatorname{Pic}^0$ with trivial tensor power but nontrivial pullback, and on translation-invariance criteria involving the rank of $H^0$ on geometric fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_subsingleton_sections_of_inPicZero_of_not_iso_unit.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.subsingleton_sections_of_inPicZero_of_not_iso_unit
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (M : A.Modules) (hM : InPicZero f L M) (hM1 : ¬ Nonempty (M ≅ 𝟙_ (A.Modules))) :
    Subsingleton (Γ(M, ⊤) : Type) := by sorry
