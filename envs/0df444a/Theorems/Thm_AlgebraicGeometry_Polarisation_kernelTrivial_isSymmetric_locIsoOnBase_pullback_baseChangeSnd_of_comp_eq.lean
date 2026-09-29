-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_kernelTrivial_isSymmetric_locIsoOnBase_pullback_baseChangeSnd_of_comp_eq
-- name    : AlgebraicGeometry.Polarisation.kernelTrivial_isSymmetric_locIsoOnBase_pullback_baseChangeSnd_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/86cc84b6-ccc3-53dc-919c-905b4794fd6b
-- title:
--   Kernel-triviality, symmetry and square-root clauses under base change
-- statement:
--   Let $S$ be a commutative ring, $f\colon A\to\operatorname{Spec}S$ a scheme over $\operatorname{Spec}S$, and $L$ a relative group law on $f$, i.e. a functorial multiplication, unit and inversion on the sets of sections $x\colon T\to A$ with $x$ followed by $f$ equal to a given $t\colon T\to\operatorname{Spec}S$. Let $\mathcal L$ be an invertible module on $A$ (locally isomorphic to the unit module). Let $B,B'$ be $S$-algebras and $\varphi\colon B\to B'$ a ring homomorphism with $\varphi\circ(S\to B)=(S\to B')$; write $A_B$ for the fibre product of $f$ and $\operatorname{Spec}$ of $S\to B$, with projections $\mathrm{pr}_A$, $\mathrm{pr}_B$, and $L_B$ for the base-changed group law, and similarly over $B'$. The morphism $\operatorname{Spec}\varphi$, regarded via the above compatibility as a morphism $\operatorname{Spec}B'\to\operatorname{Spec}B$ over $\operatorname{Spec}S$, induces through `RelPicard.baseChangeSnd` a morphism $\pi\colon A_{B'}\to A_B$. Assume $M$ is an invertible module on $A_B$ satisfying the three conditions: (i) for every commutative ring $R$, every $t\colon\operatorname{Spec}R\to\operatorname{Spec}B$ and every section $x$ of $\mathrm{pr}_B$ over $t$, if the pullback along $\mathrm{sliceAt}\,x$ of the Mumford bundle of $M$ (for $L_B$) is isomorphic to the unit module after restriction to the $\mathrm{pr}_B$-preimages of the members of some open cover of $\operatorname{Spec}B$, then $x$ is the unit section $L_B.\mathrm{one}\,t$; (ii) the pullback of $M$ along the inversion morphism of $L_B$ and $M$ itself are isomorphic over the $\mathrm{pr}_B$-preimage of some open neighbourhood of each point of $\operatorname{Spec}B$; (iii) likewise $\mathrm{pr}_A^{*}\mathcal L$ and $M$ tensored with its pullback along that inversion morphism. The conclusion is that the corresponding three conditions hold over $B'$ for the module $\pi^{*}M$ on $A_{B'}$ and the group law $L_{B'}$.
--
--   This is the base-change stability, along a homomorphism of $S$-algebras, of the three clauses defining a symmetric principal square root of $\mathcal L$: triviality of the Mumford kernel, symmetry under inversion, and the square-root relation, each in the form 'isomorphic Zariski-locally on the base'. It feeds the passage from a square root over an arbitrary field or algebra to one over a finitely generated subalgebra, used in [`AlgebraicGeometry.Polarisation.exists_finiteDimensional_principalSqrt_of_exists_faithfullyFlat_principalSqrt_of_field`](thm.html#AlgebraicGeometry.Polarisation.exists_finiteDimensional_principalSqrt_of_exists_faithfullyFlat_principalSqrt_of_field).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_kernelTrivial_isSymmetric_locIsoOnBase_pullback_baseChangeSnd_of_comp_eq.lean

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

theorem AlgebraicGeometry.Polarisation.kernelTrivial_isSymmetric_locIsoOnBase_pullback_baseChangeSnd_of_comp_eq
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (B B' : Type) [CommRing B] [CommRing B'] [Algebra S B] [Algebra S B']
    (φ : B →+* B') (hφ : φ.comp (algebraMap S B) = algebraMap S B')
    (M : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S B)))).Modules) (hM : Scheme.Modules.IsInvertible M)
    (h : KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
        (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))) M ∧
      IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
        (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))) M ∧
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B))))).obj 𝓛)
        (M ⊗ (Scheme.Modules.pullback
          (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
            (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj M)) :
    KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))
        (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B')))) ((Scheme.Modules.pullback (RelPicard.baseChangeSnd f
          (⟨Spec.map (CommRingCat.ofHom φ), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S B'))) (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj M) ∧
      IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))
        (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B')))) ((Scheme.Modules.pullback (RelPicard.baseChangeSnd f
          (⟨Spec.map (CommRingCat.ofHom φ), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S B'))) (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj M) ∧
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))).obj 𝓛)
        (((Scheme.Modules.pullback (RelPicard.baseChangeSnd f
          (⟨Spec.map (CommRingCat.ofHom φ), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S B'))) (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj M) ⊗ (Scheme.Modules.pullback
          (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))
            (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B')))))).obj ((Scheme.Modules.pullback (RelPicard.baseChangeSnd f
          (⟨Spec.map (CommRingCat.ofHom φ), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S B'))) (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj M)) := by sorry
