-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_RosatiCompatible_pullback_negMor
-- name    : AlgebraicGeometry.Polarisation.RosatiCompatible.pullback_negMor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/48d9d998-589b-5979-a4da-b9c652ed8c46
-- title:
--   Rosati compatibility is preserved by pull-back along inversion
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$, and let $L$ be a relative group law on $f$: a functorial multiplication, unit and inversion on the sets $\mathrm{SchemeHomOver}\,t\,f$ of morphisms $T \to A$ over a given $t : T \to \operatorname{Spec} S$, satisfying associativity, unit and left-inverse laws and compatible with base change along morphisms $T' \to T$ over $\operatorname{Spec} S$. Assume $L$ is commutative, i.e. $L.\mathrm{mul}\,t\,x\,y = L.\mathrm{mul}\,t\,y\,x$ for all $t$ and all points $x,y$. Let $I$ be an index type, $\mathrm{act} : I \to (A \to A)$ a family of endomorphisms with $\mathrm{act}\,x$ followed by $f$ equal to $f$ for each $x$, and assume each $\mathrm{act}\,x$ acts as a homomorphism on points: post-composition with $\mathrm{act}\,x$ carries $L.\mathrm{mul}\,t\,P\,Q$ to the product of the images of $P$ and $Q$. Let $\mathrm{star} : I \to I$ be an involution-shaped index map, and let $\mathcal{L}$ be a module on $A$ which is invertible, i.e. locally on $A$ its restriction is isomorphic to the unit module. The hypothesis is $\mathrm{RosatiCompatible}\,f\,L\,\mathcal{L}\,\mathrm{act}\,\mathrm{act\_over}\,\mathrm{star}$: for every $b \in I$, the two pull-backs of the Mumford bundle $\Lambda(\mathcal{L}) = \mathrm{add}^*\mathcal{L} \otimes (\mathrm{pr}_1^*\mathcal{L}^\vee \otimes \mathrm{pr}_2^*\mathcal{L}^\vee)$ on $A \times_{\operatorname{Spec} S} A$ along $(\mathrm{pr}_1, \mathrm{act}(b)\circ\mathrm{pr}_2)$ and along $(\mathrm{act}(\mathrm{star}\,b)\circ\mathrm{pr}_1, \mathrm{pr}_2)$ satisfy $\mathrm{LocIsoOnBase}$ over the structure morphism $\mathrm{pr}_1$ followed by $f$, that is, every point of $\operatorname{Spec} S$ has an open neighbourhood $U$ over whose preimage the two modules become isomorphic. The conclusion is that the same Rosati compatibility, with the same $\mathrm{act}$ and $\mathrm{star}$, holds for the pull-back of $\mathcal{L}$ along $\mathrm{negMor}\,f\,L$, the endomorphism of $A$ underlying $L.\mathrm{inv}\,f\,(\mathrm{idPt}\,f)$, i.e. the inversion morphism of the group law.
--
--   This is the stability of Rosati compatibility of a line bundle under pull-back by $[-1]$, resting on the isomorphism $\Lambda([-1]^*\mathcal{L}) \cong ([-1]\times[-1])^*\Lambda(\mathcal{L})$ and on the fact that $[-1]$ commutes with each $\mathrm{act}(b)$; commutativity of the group law is what makes $[-1]\times[-1]$ compatible with addition. It is used in the construction of canonical polarisation data for the quaternionic moduli problem, where a candidate bundle is replaced by its tensor product with its pull-back along inversion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_RosatiCompatible_pullback_negMor.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.RosatiCompatible.pullback_negMor
    {S : Type} [CommRing S] {A : Scheme} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative)
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f)
    (act_hom : ∀ (x : I) {T : Scheme} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (star : I → I) (𝓛 : A.Modules) (h : Scheme.Modules.IsInvertible 𝓛)
    (hR : RosatiCompatible f L 𝓛 act act_over star) :
    RosatiCompatible f L ((Scheme.Modules.pullback (negMor f L)).obj 𝓛) act act_over star := by sorry
