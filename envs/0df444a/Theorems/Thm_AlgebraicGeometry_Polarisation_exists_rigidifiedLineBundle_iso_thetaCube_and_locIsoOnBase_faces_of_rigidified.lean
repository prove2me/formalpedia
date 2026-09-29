-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_rigidifiedLineBundle_iso_thetaCube_and_locIsoOnBase_faces_of_rigidified
-- name    : AlgebraicGeometry.Polarisation.exists_rigidifiedLineBundle_iso_thetaCube_and_locIsoOnBase_faces_of_rigidified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/c42cca10-81e8-536d-b562-04b095c13ed1
-- title:
--   Theta-cube of a rigidified bundle: rigidification and trivial faces
-- statement:
--   Let $S$ be a commutative ring, $f : A \to \operatorname{Spec} S$ a morphism of schemes carrying a relative group law $L$ (functorial multiplication, unit, inverse on $T$-points over $\operatorname{Spec} S$) which is commutative, and assume $f$ satisfies `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, all fibres $f^{-1}(s)$ are connected, and $f$ admits a relative group law. Let $\iota : \operatorname{Spec} R \to \operatorname{Spec} S$ be given, write $g := \operatorname{pr}_2 : B := A \times_S \operatorname{Spec} R \to \operatorname{Spec} R$ with the base-changed law `L.baseChange ι`, and let $N$ be an invertible module on $B$ rigidified along the unit section of $f$ over $\operatorname{Spec} R$. Put $\Lambda := \mu^*N \otimes (\operatorname{pr}_1^*N^\vee \otimes \operatorname{pr}_2^*N^\vee)$, the Mumford bundle on $B\times_R B$, where $\mu$ is the addition morphism of the base-changed law. Then there exists an invertible module $M$ on $(B\times_R B)\times_R B$, rigidified along the section $b \mapsto ((e,e),b)$ given by the unit of the product law on $B\times_R B$, such that: (i) $M$ is isomorphic to $(\mu_{12},\operatorname{pr}_3)^*\Lambda \otimes \bigl(((\operatorname{pr}_1,\operatorname{pr}_3)^*\Lambda)^\vee \otimes ((\operatorname{pr}_2,\operatorname{pr}_3)^*\Lambda)^\vee\bigr)$; and (ii) the pull-backs of $M$ along the three face maps $(x,y)\mapsto((e,x),y)$, $(x,y)\mapsto((x,e),y)$ and $(x,y)\mapsto((x,y),e)$ of $B\times_R B$ are each locally isomorphic to the unit module over the base, in the sense that every point $s$ of $\operatorname{Spec} R$ has an open neighbourhood $U$ over whose preimage in $B\times_R B$ the restriction of the pull-back is isomorphic to the restricted unit module.
--
--   This is the form in which the theorem of the cube enters the construction of polarisations: the theta-cube $\Theta(N)$ built from the Mumford bundle $\Lambda(N)$ is exhibited as a rigidified line bundle whose three coordinate faces are trivial over the base, the hypotheses under which a cube bundle is to be shown trivial. It is used in the proof that, for a rigidified line bundle on an abelian scheme, the pull-back along multiplication by $2$ decomposes as a tensor product involving the pull-back along the inverse morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_rigidifiedLineBundle_iso_thetaCube_and_locIsoOnBase_faces_of_rigidified.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.Polarisation.exists_rigidifiedLineBundle_iso_thetaCube_and_locIsoOnBase_faces_of_rigidified
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι) :
    ∃ M : RigidifiedLineBundle (prodStr (pullback.snd f ι) (pullback.snd f ι)) (((L.baseChange ι).prod (L.baseChange ι)).one (𝟙 (Spec (CommRingCat.of R)))) (pullback.snd f ι),
      Nonempty (M.L ≅ ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ addMor (pullback.snd f ι) (L.baseChange ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc, addMor_over]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L) ⊗
      (Scheme.Modules.dual ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ pullback.fst (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L)) ⊗
       Scheme.Modules.dual ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ pullback.snd (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc, ← pullback.condition (f := (pullback.snd f ι)) (g := (pullback.snd f ι))]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L))))) ∧
      LocIsoOnBase (prodStr (pullback.snd f ι) (pullback.snd f ι))
        ((Scheme.Modules.pullback
          (pullback.lift
            (pullback.lift ((L.baseChange ι).one (prodStr (pullback.snd f ι) (pullback.snd f ι))).1 (pullback.fst (pullback.snd f ι) (pullback.snd f ι)) (by rw [((L.baseChange ι).one _).2]))
            (pullback.snd (pullback.snd f ι) (pullback.snd f ι))
            (by rw [pullback.lift_fst_assoc, ((L.baseChange ι).one _).2]; exact pullback.condition))).obj M.L) (𝟙_ _) ∧
      LocIsoOnBase (prodStr (pullback.snd f ι) (pullback.snd f ι))
        ((Scheme.Modules.pullback
          (pullback.lift
            (pullback.lift (pullback.fst (pullback.snd f ι) (pullback.snd f ι)) ((L.baseChange ι).one (prodStr (pullback.snd f ι) (pullback.snd f ι))).1 (by rw [((L.baseChange ι).one _).2]))
            (pullback.snd (pullback.snd f ι) (pullback.snd f ι))
            (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj M.L) (𝟙_ _) ∧
      LocIsoOnBase (prodStr (pullback.snd f ι) (pullback.snd f ι))
        ((Scheme.Modules.pullback
          (pullback.lift (𝟙 _) ((L.baseChange ι).one (prodStr (pullback.snd f ι) (pullback.snd f ι))).1 (by rw [Category.id_comp, ((L.baseChange ι).one _).2]))).obj M.L) (𝟙_ _) := by sorry
