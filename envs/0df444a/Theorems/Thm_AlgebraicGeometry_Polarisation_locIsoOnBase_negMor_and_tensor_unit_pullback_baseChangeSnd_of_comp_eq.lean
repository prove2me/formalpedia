-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_negMor_and_tensor_unit_pullback_baseChangeSnd_of_comp_eq
-- name    : AlgebraicGeometry.Polarisation.locIsoOnBase_negMor_and_tensor_unit_pullback_baseChangeSnd_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/20dd30b0-fec3-56d5-8367-5b3bb5dd2fde
-- title:
--   Local symmetry and trivial square ascend along base change
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f\colon A\to\operatorname{Spec} S$, equipped with a relative group law $L$ on $f$ (functorial multiplication, unit and inversion on the sets of sections $\operatorname{SchemeHomOver} t\,f$ for test bases $t$, satisfying associativity, unit, inverse and naturality laws). Let $B,B'$ be commutative $S$-algebras and $\varphi\colon B\to B'$ a ring homomorphism with $\varphi\circ(\text{structure map of }B)=$ the structure map of $B'$, so that $\operatorname{Spec}\varphi$ is a morphism $\operatorname{Spec} B'\to\operatorname{Spec} B$ over $\operatorname{Spec} S$. Let $N$ be a module on $A_B:=A\times_{\operatorname{Spec} S}\operatorname{Spec} B$ which is invertible, i.e. every point has an open neighbourhood over which $N$ pulls back to the unit module. Assume, for the second projection $A_B\to\operatorname{Spec} B$, that both pairs $\bigl((-1)^*N,\,N\bigr)$ and $\bigl(N\otimes N,\,\mathbf 1\bigr)$ are locally isomorphic on the base, where $(-1)$ is the inversion morphism `negMor` of the base-changed law $L$ over $B$: for every point of $\operatorname{Spec} B$ there is an open neighbourhood $U$ such that the two modules become isomorphic after restriction to the preimage of $U$. The conclusion is the same pair of local-on-the-base statements over $\operatorname{Spec} B'$ for the pullback of $N$ along the base-change morphism $A_{B'}\to A_B$ given by the identity on $A$ and $\operatorname{Spec}\varphi$ on the base, with the inversion morphism of $L$ base-changed to $B'$.
--
--   This is the stability under change of test algebra of the admissibility conditions on an invertible module — symmetry under inversion and triviality of the square, both only locally on the base — the conditions cutting out symmetric $2$-torsion line bundles in the sense of Mumford's theory of $K(\mathcal L)$ and the Cartier dual of $A[2]$. It supplies the base-change datum for the functor of rigidified admissible bundles used in [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_finite_faithfullyFlat_corepresents_symmRoot_classFunctor_under`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_finite_faithfullyFlat_corepresents_symmRoot_classFunctor_under).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_negMor_and_tensor_unit_pullback_baseChangeSnd_of_comp_eq.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.locIsoOnBase_negMor_and_tensor_unit_pullback_baseChangeSnd_of_comp_eq
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (B B' : Type) [CommRing B] [CommRing B'] [Algebra S B] [Algebra S B']
    (φ : B →+* B') (hφ : φ.comp (algebraMap S B) = algebraMap S B')
    (N : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S B)))).Modules) (hN : Scheme.Modules.IsInvertible N)
    (h : LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
        ((Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
          (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj N) N ∧
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
        (N ⊗ N) (𝟙_ ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap S B)))).Modules))) :
    LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))
        ((Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))
          (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B')))))).obj ((Scheme.Modules.pullback (RelPicard.baseChangeSnd f
          (⟨Spec.map (CommRingCat.ofHom φ), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S B'))) (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj N)) ((Scheme.Modules.pullback (RelPicard.baseChangeSnd f
          (⟨Spec.map (CommRingCat.ofHom φ), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S B'))) (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj N) ∧
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))
        (((Scheme.Modules.pullback (RelPicard.baseChangeSnd f
          (⟨Spec.map (CommRingCat.ofHom φ), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S B'))) (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj N) ⊗ ((Scheme.Modules.pullback (RelPicard.baseChangeSnd f
          (⟨Spec.map (CommRingCat.ofHom φ), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S B'))) (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj N)) (𝟙_ ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap S B')))).Modules)) := by sorry
