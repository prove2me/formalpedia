-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_transportIso_tensorObj
-- name    : AlgebraicGeometry.RiemannForm.transportIso_tensorObj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/c0439979-1a17-5cb7-95a2-3d060e80cd36
-- title:
--   Monoidality of the transport isomorphism along g ∘ T = g
-- statement:
--   Let $A$ be a scheme (in universe $0$), let $T, g : A \to A$ be morphisms of schemes satisfying $h : T$ followed by $g$ equals $g$, and let $M, M'$ be objects of the category $A.\mathrm{Modules}$ of $\mathcal{O}_A$-modules. Here $\mathrm{transportIso}\,h\,N : T^{*}g^{*}N \cong g^{*}N$ denotes, for an $\mathcal{O}_A$-module $N$, the composite of the component at $N$ of the comparison isomorphism $T^{*}\circ g^{*} \cong (T \mathbin{\text{then}} g)^{*}$ with the component at $N$ of the isomorphism of pullback functors induced by the equality $h$; and $\mathrm{pullbackTensorObjIso}\,f\,L\,M : f^{*}(L \otimes M) \cong f^{*}L \otimes f^{*}M$ is the inverse of the monoidal-structure isomorphism of the pullback functor along $f$. The assertion is an equality of isomorphisms $T^{*}g^{*}(M \otimes M') \cong g^{*}(M \otimes M')$: the transport isomorphism $\mathrm{transportIso}\,h\,(M \otimes M')$ coincides with the composite $$T^{*}g^{*}(M \otimes M') \to T^{*}(g^{*}M \otimes g^{*}M') \to T^{*}g^{*}M \otimes T^{*}g^{*}M' \to g^{*}M \otimes g^{*}M' \to g^{*}(M \otimes M'),$$ whose steps are, in order: $T^{*}$ applied to $\mathrm{pullbackTensorObjIso}\,g\,M\,M'$, the isomorphism $\mathrm{pullbackTensorObjIso}\,T$ at the pair $(g^{*}M, g^{*}M')$, the tensor product of $\mathrm{transportIso}\,h\,M$ with $\mathrm{transportIso}\,h\,M'$, and the inverse of $\mathrm{pullbackTensorObjIso}\,g\,M\,M'$.
--
--   This records that the transport identification attached to an endomorphism $T$ of $A$ with $g \circ T = g$ is compatible with tensor products, i.e. is monoidal for the induced monoidal structures on the pullback functors. It is used in the construction of the level pairing attached to a Riemann form, where multiplicativity of a pairing value under an isomorphism of tensor products is needed ([`AlgebraicGeometry.RiemannForm.isLevelPairingValue_mul_of_iso_tensor`](thm.html#AlgebraicGeometry.RiemannForm.isLevelPairingValue_mul_of_iso_tensor)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_transportIso_tensorObj.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.transportIso_tensorObj
    {A : Scheme.{0}} {T g : A ⟶ A} (h : T ≫ g = g) (M M' : A.Modules) :
    transportIso h (M ⊗ M') =
      (Scheme.Modules.pullback T).mapIso (Scheme.Modules.pullbackTensorObjIso g M M') ≪≫
        Scheme.Modules.pullbackTensorObjIso T ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj M') ≪≫
        (transportIso h M ⊗ᵢ transportIso h M') ≪≫
        (Scheme.Modules.pullbackTensorObjIso g M M').symm := by sorry
