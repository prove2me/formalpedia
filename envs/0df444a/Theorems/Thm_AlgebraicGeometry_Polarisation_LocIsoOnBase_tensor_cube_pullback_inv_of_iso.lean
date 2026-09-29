-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_tensor_cube_pullback_inv_of_iso
-- name    : AlgebraicGeometry.Polarisation.LocIsoOnBase.tensor_cube_pullback_inv_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/6d29db89-3ca5-54b4-bc12-7011415f2c82
-- title:
--   Local cube structure transported along an isomorphism over the base
-- statement:
--   Let $S$ be a commutative ring, let $A$ and $A'$ be schemes with morphisms $f : A \to \operatorname{Spec} S$ and $f' : A' \to \operatorname{Spec} S$, and let $e : A \cong A'$ be an isomorphism of schemes with $f' \circ e = f$ (written in diagrammatic order as $e_{\mathrm{hom}}$ followed by $f'$ equal to $f$). Let $P$ and $M$ be objects of $A.\mathrm{Modules}$ and $P'$ an object of $A'.\mathrm{Modules}$. Assume $\mathrm{LocIsoOnBase}\ f\ P\ (M \otimes M \otimes M)$ and $\mathrm{LocIsoOnBase}\ f\ (e_{\mathrm{hom}}^* P')\ P$, where $\mathrm{LocIsoOnBase}\ g\ N\ N'$ means: for every point $s$ of $\operatorname{Spec} S$ there is an open $U \subseteq \operatorname{Spec} S$ with $s \in U$ such that the pullbacks of $N$ and of $N'$ along the inclusion of the open subscheme $g^{-1}(U)$ into the source are isomorphic. The conclusion is $\mathrm{LocIsoOnBase}\ f'\ P'\ (M' \otimes M' \otimes M')$ with $M' := e_{\mathrm{inv}}^* M$, i.e. locally over the base $\operatorname{Spec} S$ the module $P'$ becomes isomorphic to the triple tensor product of the pullback of $M$ along $e^{-1}$.
--
--   This is the transport step for the property of being locally on the base a tensor cube, used when comparing two presentations of the same polarisation datum under an isomorphism of abelian schemes over $\operatorname{Spec} S$. It is invoked in the comparison of quaternionic multiplication structures, in particular in [`AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_iso_of_polarisedAbelianScheme_iso`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_iso_of_polarisedAbelianScheme_iso) and in the criterion `withFullLevel_iso_iff_iso_of_packages_of_isUnit_two`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_tensor_cube_pullback_inv_of_iso.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.LocIsoOnBase.tensor_cube_pullback_inv_of_iso
    {S : Type u} [CommRing S] {A A' : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
    (e : A ≅ A') (he : e.hom ≫ f' = f) (P M : A.Modules) (P' : A'.Modules)
    (hP : LocIsoOnBase f P (M ⊗ M ⊗ M))
    (hPP' : LocIsoOnBase f ((Scheme.Modules.pullback e.hom).obj P') P) :
    LocIsoOnBase f' P'
      ((Scheme.Modules.pullback e.inv).obj M ⊗ (Scheme.Modules.pullback e.inv).obj M ⊗ (Scheme.Modules.pullback e.inv).obj M) := by sorry
