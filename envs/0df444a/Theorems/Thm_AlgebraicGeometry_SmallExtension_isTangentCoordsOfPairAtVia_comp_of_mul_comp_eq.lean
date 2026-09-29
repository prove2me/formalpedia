-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_comp_of_mul_comp_eq
-- name    : AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_mul_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/b647c42f-0e89-527d-9397-b98e23b561fd
-- title:
--   Covariance of pair tangent coordinates along a fibre homomorphism
-- statement:
--   Fix a local ring $T'$ with residue field $k$, an ideal $I\subseteq T'$, a $k$-module $V$ carrying a central right $k$-action together with a compatible $T'$-module structure, a $T'$-linear map $\iota : V \to T'$, and a $T'$-algebra $C$. On the source side let $u,v : \operatorname{Spec} C \to Z$ be two morphisms, $f_{X_k} : X_k \to \operatorname{Spec} k$ a morphism equipped with a `RelativeGroupLaw` $L^X$ (a functorial group structure on the sets of morphisms to $X_k$ over $\operatorname{Spec} k$), $W^X \subseteq X_k$ open with $a^X : W^X \to Z$, and $U^X_e \subseteq X_k$ open; on the target side let $f_k : A_k \to \operatorname{Spec} k$ carry a relative group law $L^A$, with $W^A \subseteq A_k$ open, $a^A : W^A \to Y$ and $U_e \subseteq A_k$ open. Let $H : Z \to Y$ and $h_k : X_k \to A_k$ satisfy $h_k$ followed by $f_k$ equal to $f_{X_k}$ and be a homomorphism on points: for every $t : S \to \operatorname{Spec} k$ and all $t$-points $P,Q$ of $f_{X_k}$, the underlying morphism of $L^X$-product $P\cdot Q$ followed by $h_k$ equals the underlying morphism of the $L^A$-product of $P$ followed by $h_k$ and $Q$ followed by $h_k$. Assume $U^X_e \le h_k^{-1}U_e$, $W^X \le h_k^{-1}W^A$, and the compatibility that the inclusion $W^X \le h_k^{-1}W^A$ followed by the restricted morphism $h_k\mid_{W^A}$ and then $a^A$ equals $a^X$ followed by $H$. Let $c : \Gamma(X_k,U^X_e) \to \operatorname{Hom}_k(\operatorname{Hom}_k(V,k),\,k\otimes_{T'}C)$ satisfy `IsTangentCoordsOfPairAtVia` for $(I,V,\iota,C,u,v,f_{X_k},L^X,W^X,a^X,U^X_e)$, i.e. there are a point $w_0$ of $W^X$ and a point $w_1$ of $U^X_e$ with values in $\operatorname{Spec}$ of the thickening $(k\otimes_{T'}C)\otimes_k(k\oplus V)$ such that $w_0$ followed by the inclusion and $f_{X_k}$ is the prescribed base morphism, $w_0$ followed by $a^X$ is a tangent vector of the pair $(u,v)$ (it factors as $\operatorname{Spec}\vartheta$ followed by some $\varphi : \operatorname{Spec}(\mathrm{pairRing}\,I\,C) \to Z$ for a Schlessinger ring map $\vartheta$, where the two projections of the pair ring pull $\varphi$ back to $u$ and $v$), $w_1$ is the $L^X$-translate of $w_0$ in $A_k$'s sense on the source side, and $c$ is the tangent-coordinate function attached to the chart homomorphism of $w_1$. The conclusion is that the same predicate holds on the target side for $(u$ followed by $H$, $v$ followed by $H)$, $f_k$, $L^A$, $W^A$, $a^A$, $U_e$, with coordinate function $a \mapsto c$ applied to the restriction to $U^X_e$ of the pullback $h_k^\sharp a$ of $a \in \Gamma(A_k,U_e)$.
--
--   This is the covariance (functoriality) of the canonical tangent coordinates of a pair along a homomorphism of special fibres together with a compatible morphism of the ambient schemes: classically, the differential of a homomorphism of group schemes, read in the translation trivialisations on both sides, is given at the level of functions near the unit by precomposition with $h_k^\sharp$. It is used in the two-cocycle computation for the obstruction attached to unit pullbacks, where $H$ plays the role of a chartwise lift of $h_k$ over $T'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_comp_of_mul_comp_eq.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct
  AlgebraicGeometry.SmallExtension Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_mul_comp_eq
    {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (C : Type u) [CommRing C] [Algebra T' C]

    {Z : Scheme.{u}} (u v : Spec (CommRingCat.of C) ⟶ Z)
    {Xk : Scheme.{u}} (fXk : Xk ⟶ Spec (CommRingCat.of (ResidueField T'))) (LX : RelativeGroupLaw (ResidueField T') fXk)
    (WX : Xk.Opens) (aWX : (WX : Scheme.{u}) ⟶ Z) (UXe : Xk.Opens)

    {Y : Scheme.{u}}
    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') fk)
    (WA : Ak.Opens) (aWA : (WA : Scheme.{u}) ⟶ Y) (Ue : Ak.Opens)

    (H : Z ⟶ Y)
    (hk : Xk ⟶ Ak) (hhkf : hk ≫ fk = fXk)
    (hhom : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of (ResidueField T'))) (P Q : SchemeHomOver t fXk),
      (LX.mul t P Q).1 ≫ hk =
        (Lk.mul t ⟨P.1 ≫ hk, by rw [Category.assoc, hhkf, P.2]⟩ ⟨Q.1 ≫ hk, by rw [Category.assoc, hhkf, Q.2]⟩).1)
    (hUX : UXe ≤ hk ⁻¹ᵁ Ue) (hW : WX ≤ hk ⁻¹ᵁ WA)
    (hcompat : Xk.homOfLE hW ≫ (hk ∣_ WA) ≫ aWA = aWX ≫ H)
    (c : Γ(Xk, UXe) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (hc : IsTangentCoordsOfPairAtVia I V ι C u v fXk LX WX aWX UXe c) :
    IsTangentCoordsOfPairAtVia I V ι C (u ≫ H) (v ≫ H) fk Lk WA aWA Ue
      (fun a => c ((Xk.presheaf.map (homOfLE hUX).op).hom ((hk.app Ue).hom a))) := by sorry
