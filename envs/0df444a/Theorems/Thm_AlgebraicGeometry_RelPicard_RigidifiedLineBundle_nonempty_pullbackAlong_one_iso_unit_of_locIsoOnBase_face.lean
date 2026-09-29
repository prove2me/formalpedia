-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_pullbackAlong_one_iso_unit_of_locIsoOnBase_face
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_pullbackAlong_one_iso_unit_of_locIsoOnBase_face
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/34992163-5e42-5240-b477-c4f9d3c1edd1
-- title:
--   Triviality of e^*M from local triviality of the third face
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism, and let $L$ be a `RelativeGroupLaw` for $f$: a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of points of $A$ over arbitrary bases $t : T \to \operatorname{Spec} S$, with unit sections `L.one t`, inverses, the group axioms and naturality under base change. Assume `AbelianSchemePropertyBundle S f`, i.e. $f$ is smooth and proper, each fibre of $f$ is connected, and $f$ admits a relative group law. Write $c =$ `prodStr f f` $= \mathrm{pr}_1 \circ f$ for the structure morphism of $A \times_S A$, and let $M$ be a rigidified line bundle on $c$ with parameter $f$ and rigidification along the identity section of the product group law `L.prod L`: thus $M$ consists of a module $M.L$ on the pullback of $c$ and $f$ which is locally on that scheme isomorphic to the unit, together with a trivialisation of its pullback along the rigidifying section. Let $\iota : A \times_S A \to (A \times_S A) \times_S A$ be the face $(x,y) \mapsto (x,y,\,e(x,y))$, given by the identity and the unit section `L.one c`, and assume `LocIsoOnBase` for $c$ between $\iota^* M.L$ and the monoidal unit, i.e. every point of $\operatorname{Spec} S$ has an open neighbourhood $U$ over whose preimage the two modules become isomorphic. The conclusion is that the underlying module of the pullback of $M$ along the identity point `L.one (𝟙)` is isomorphic (non-emptiness of the type of isomorphisms) to the underlying module of the unit rigidified bundle with parameter $\mathbf{1}_{\operatorname{Spec} S}$.
--
--   This is the rigidity step of the theorem of the cube in the form used for the relative Picard functor: local triviality on the base of the restriction of $M$ to the third face $A \times_S A \times \{e\}$ forces the pullback $e^*M$ to be globally trivial. It feeds the combination of the three faces in [`AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_unit_of_locIsoOnBase_unit_faces_of_isNoetherianRing`](thm.html#AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_unit_of_locIsoOnBase_unit_faces_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_pullbackAlong_one_iso_unit_of_locIsoOnBase_face.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_pullbackAlong_one_iso_unit_of_locIsoOnBase_face
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (M : RigidifiedLineBundle (prodStr f f) ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f)
    (h₃ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift (𝟙 _) (L.one (prodStr f f)).1 (by rw [Category.id_comp, (L.one _).2]))).obj M.L) (𝟙_ _)) :
    Nonempty ((M.pullbackAlong (L.one (𝟙 (Spec (CommRingCat.of S))))).L ≅
      (RigidifiedLineBundle.unit (c := prodStr f f) (ε := (L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) (𝟙 _)).L) := by sorry
