-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_pullback_baseChangeSnd_of_comp_eq
-- name    : AlgebraicGeometry.Polarisation.isSymmetric_locIsoOnBase_pullback_baseChangeSnd_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/1681d768-79f9-5cef-81d5-1454b203efd7
-- title:
--   Symmetry and local square-root clauses under base change
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, $f\colon A\to\operatorname{Spec}S$ a morphism, and $L$ a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi\colon T\to A \mid \varphi\circ f = t\}$ of $A$-valued points over varying $t\colon T\to\operatorname{Spec}S$, natural in $T$. Let $\mathcal L$ be an invertible module on $A$ (locally isomorphic to the unit), let $B,B'$ be $S$-algebras and $\varphi\colon B\to B'$ a ring homomorphism with $\varphi\circ(S\to B)=(S\to B')$, and let $M$ be an invertible module on $A_B=A\times_{\operatorname{Spec}S}\operatorname{Spec}B$. Assume, for the base-changed law $L_B$ on the structure map $A_B\to\operatorname{Spec}B$, that (i) $[-1]^*M$ and $M$ are isomorphic locally on the base, meaning every point of $\operatorname{Spec}B$ has an open neighbourhood $U$ over whose preimage the two restrictions are isomorphic, and (ii) the pullback of $\mathcal L$ to $A_B$ along the first projection is, in the same local-on-$\operatorname{Spec}B$ sense, isomorphic to $M\otimes[-1]^*M$. Then the pullback of $M$ along $\mathrm{id}_A\times\operatorname{Spec}\varphi\colon A_{B'}\to A_B$ satisfies both clauses over $B'$ for the law $L_{B'}$: it is symmetric, and its tensor product with its $[-1]$-pullback is locally on $\operatorname{Spec}B'$ isomorphic to the pullback of $\mathcal L$ to $A_{B'}$.
--
--   This is the base-change functoriality, in the test $S$-algebra, of the two conditions defining a symmetric square root of $\mathcal L$ locally on the base. It is used in the construction of such square roots after a finite faithfully flat cover, in the existence statement [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_finite_faithfullyFlat_atPrime_isSymmetric_locIsoOnBase_of_faithfullyFlat`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_finite_faithfullyFlat_atPrime_isSymmetric_locIsoOnBase_of_faithfullyFlat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_pullback_baseChangeSnd_of_comp_eq.lean

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

theorem AlgebraicGeometry.Polarisation.isSymmetric_locIsoOnBase_pullback_baseChangeSnd_of_comp_eq
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (B B' : Type) [CommRing B] [CommRing B'] [Algebra S B] [Algebra S B']
    (φ : B →+* B') (hφ : φ.comp (algebraMap S B) = algebraMap S B')
    (M : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S B)))).Modules) (hM : Scheme.Modules.IsInvertible M)
    (h : IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
        (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))) M ∧
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B))))).obj 𝓛)
        (M ⊗ (Scheme.Modules.pullback
          (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
            (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj M)) :
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
