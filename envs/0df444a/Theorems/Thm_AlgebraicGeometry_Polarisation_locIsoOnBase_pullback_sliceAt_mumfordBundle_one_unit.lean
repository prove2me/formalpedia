-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_pullback_sliceAt_mumfordBundle_one_unit
-- name    : AlgebraicGeometry.Polarisation.locIsoOnBase_pullback_sliceAt_mumfordBundle_one_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/73393efe-1ae3-50a7-8a47-dc7a3e169539
-- title:
--   Slice of the Mumford bundle at the unit is locally trivial
-- statement:
--   Let $k$ be a field (assumed algebraically closed), let $f : A \to \operatorname{Spec} k$ be a scheme over $k$ equipped with a relative group law $L$, i.e. functorial multiplication, unit and inverse operations on $T$-points over $\operatorname{Spec} k$ satisfying associativity, the unit laws, left inversion and naturality in $T$; let $\mathcal L$ be a module on $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ with $\mathcal L|_U$ isomorphic to the unit module of $U$; let $R$ be a commutative ring and $t : \operatorname{Spec} R \to \operatorname{Spec} k$ a morphism. Write $e = L.\mathrm{one}\,t$ for the unit $R$-point of $A$, $\sigma = \mathrm{sliceAt}\,f\,e : A \times_k \operatorname{Spec} R \to A \times_k A$ for the morphism with components $\mathrm{pr}_1$ and $\mathrm{pr}_2$ followed by $e$, and $\Lambda(\mathcal L) = \mu^*\mathcal L \otimes (p_1^*\mathcal L^\vee \otimes p_2^*\mathcal L^\vee)$ for the Mumford bundle on $A\times_k A$, where $\mu$ is the morphism given by the group law applied to the two projections and $\mathcal L^\vee$ is the internal hom from $\mathcal L$ to the unit module. The conclusion is that $\sigma^*\Lambda(\mathcal L)$ and the unit module on $A\times_k\operatorname{Spec} R$ are isomorphic locally on the base along $\mathrm{pr}_2 : A\times_k \operatorname{Spec} R \to \operatorname{Spec} R$: for every point $s$ of $\operatorname{Spec} R$ there is an open $U \ni s$ such that the restrictions of the two modules to $\mathrm{pr}_2^{-1}(U)$ are isomorphic.
--
--   This is the statement that the unit section lies in $K(\mathcal L)$, in the form appropriate to $R$-valued points: the slice of the Mumford (theorem-of-the-square) bundle at the unit point is trivial locally on the base. It supplies one implication in the characterisation of the kernel of $\varphi_{\mathcal L}$ by local triviality of slices of $\Lambda(\mathcal L)$, and is used in the treatment of two-torsion of that kernel and of the inverse-and-dual comparison for such slices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_pullback_sliceAt_mumfordBundle_one_unit.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.locIsoOnBase_pullback_sliceAt_mumfordBundle_one_unit
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of k)) :
    LocIsoOnBase (pullback.snd f t) ((Scheme.Modules.pullback (sliceAt f (L.one t))).obj (mumfordBundle f L 𝓛)) (𝟙_ ((pullback f t).Modules)) := by sorry
