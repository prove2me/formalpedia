-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_schemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced
-- name    : AlgebraicGeometry.RelPicard.schemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/c652f361-d723-5ff8-ad74-08c32ec138b5
-- title:
--   Rigidity over ℤ_{(ℓ)}: agreement on ℚ̄-points suffices
-- statement:
--   Let $\ell$ be a prime and let $R = \mathbf{Z}_{(\ell)}$ be realised as the subring [`GaloisRep.ratLocalizedAt`](def/GaloisRep_Flat.html#L8) $\ell$ of $\mathbf{Q}$ consisting of those rationals whose denominator is coprime to $\ell$. Let $c \colon X \to \operatorname{Spec} R$ be a morphism of schemes that is proper, smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a section of $c$, that is, a morphism $\operatorname{Spec} R \to X$ whose composite with $c$ is the identity. Let $D$ consist of a scheme $D.P$, a structure morphism $D.toBase \colon D.P \to \operatorname{Spec} R$ and a section $D.zeroSection$ of it, and assume `RepresentsRelSubPic` holds for $c$, $\varepsilon$, the cut `algEquivZeroCut` and $D$: there is a rigidified line bundle (an invertible module on $X \times_{\operatorname{Spec} R} D.P$ whose restriction along the $\varepsilon$-rigidification section is isomorphic to the unit) which is fibrewise algebraically equivalent to zero, i.e. on each geometric fibre over a point $\operatorname{Spec} k \to D.P$ with $k$ algebraically closed, such that every rigidified line bundle on $X \times_{\operatorname{Spec} R} T$ with the same fibrewise property is induced, via pullback, by a unique morphism $T \to D.P$ over $\operatorname{Spec} R$, the zero section inducing the unit bundle. Assume moreover that $D.toBase$ is smooth, proper and geometrically connected, and that $D.P$ is reduced. Then any two morphisms $\varphi, \psi \colon D.P \to D.P$ over $\operatorname{Spec} R$ which satisfy $\varphi \circ x = \psi \circ x$ for every morphism $x \colon \operatorname{Spec} \overline{\mathbf{Q}} \to D.P$ lying over the structure morphism $\operatorname{Spec} \overline{\mathbf{Q}} \to \operatorname{Spec} R$ coming from the inclusion $R \subset \overline{\mathbf{Q}}$ are equal.
--
--   This is the rigidity statement for the relative $\mathrm{Pic}^0$ of a smooth proper curve over $\mathbf{Z}_{(\ell)}$: an endomorphism of the representing scheme over the base is determined by its effect on $\overline{\mathbf{Q}}$-valued points, with no group-law or homomorphism hypothesis, and with reducedness of the representing scheme assumed as a hypothesis. It is used by [`AlgebraicGeometry.RelPicard.schemeHomOver_ext_of_forall_algebraicClosure_point`](thm.html#AlgebraicGeometry.RelPicard.schemeHomOver_ext_of_forall_algebraicClosure_point), which removes that hypothesis, and thereby serves to pin down endomorphisms of the relative Jacobian that are specified only on geometric points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_schemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
set_option maxHeartbeats 800000 in

theorem AlgebraicGeometry.RelPicard.schemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced
    (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)
    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase)
    [IsReduced D.P]
    (φ ψ : SchemeHomOver D.toBase D.toBase)
    (h : ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) D.toBase,
      x.1 ≫ φ.1 = x.1 ≫ ψ.1) :
    φ = ψ := by sorry
