-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_principalSqrt_of_exists_pullback_of_faithfullyFlat
-- name    : AlgebraicGeometry.Polarisation.exists_faithfullyFlat_principalSqrt_of_exists_pullback_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/9901d700-4b80-5591-adb1-5e65dcd50d0a
-- title:
--   Fppf-local principal square roots descend along faithfully flat base change
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, $f : A \to \operatorname{Spec} S$ a morphism and $L$ a relative group law on $f$, that is, a group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over each $t : T \to \operatorname{Spec} S$, natural in $T$. Let $S'$ be an $S$-algebra which is faithfully flat as an $S$-module, write $p : A \times_{\operatorname{Spec} S} \operatorname{Spec} S' \to \operatorname{Spec} S'$ for the second projection and $\mathrm{pr}$ for the first, and let $L'$ be a relative group law on $p$ such that for all $T$, all $t' : T \to \operatorname{Spec} S'$ and all points $P,Q$ over $t'$ one has $\mathrm{pr} \circ L'.\mathrm{mul}(P,Q) = L.\mathrm{mul}(\mathrm{pr}\circ P, \mathrm{pr}\circ Q)$, i.e. $\mathrm{pr}$ is a homomorphism on points. Let $\mathcal L$ be an invertible module on $A$ (locally isomorphic to the unit). Say that a module $\mathcal M$ on a scheme over a base ring $R$ carrying a group law *admits a principal square root fppf-locally* if there is a faithfully flat $R$-algebra $R_1$ such that for every relative group law $L_1$ on the base change to $R_1$ compatible with the given one along the first projection, there is an invertible module $\mathcal L_0$ on the base change with `KernelTrivial` — for every ring $R'$, every $t : \operatorname{Spec} R' \to \operatorname{Spec} R_1$ and every point $x$ over $t$, if the pullback of the Mumford bundle of $\mathcal L_0$ along the slice at $x$ is isomorphic to the unit locally on the base, then $x$ is the unit point — and such that the pullback of $\mathcal M$ and $\mathcal L_0 \otimes [-1]^{*}\mathcal L_0$ are isomorphic over the preimages of a neighbourhood of each point of $\operatorname{Spec} R_1$ (here $[-1]$ is the inversion morphism attached to $L_1$). The theorem asserts: if $\mathrm{pr}^{*}\mathcal L$ on $p$, with the law $L'$, admits a principal square root fppf-locally, then so does $\mathcal L$ on $f$ with the law $L$.
--
--   This is the descent step for the fppf-local principal square root clause in the theory of polarisations given by Mumford bundles: the clause may be verified after a faithfully flat base change, the two covers being composed. It is used in the Čerednik–Drinfeld fake elliptic curve material, by [`CerednikDrinfeld.QM.FakeEllipticCurve.isCanonicalPol_of_locIsoOnBase_pullback_of_faithfullyFlat`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.isCanonicalPol_of_locIsoOnBase_pullback_of_faithfullyFlat), to recognise a canonical polarisation after base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_principalSqrt_of_exists_pullback_of_faithfullyFlat.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.exists_faithfullyFlat_principalSqrt_of_exists_pullback_of_faithfullyFlat
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (S' : Type u) [CommRing S'] [Algebra S S'] (hff : Module.FaithfullyFlat S S')
    (L' : RelativeGroupLaw S' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))))
    (hL' : (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S'))
            (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
            (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
              (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : (∃ (S₂ : Type u) (_ : CommRing S₂) (_ : Algebra S' S₂),
      Module.FaithfullyFlat S' S₂ ∧
      ∀ (L₂ : RelativeGroupLaw S₂ (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))))),
        (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S₂)) (P Q : SchemeHomOver t' (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))))),
            (L₂.mul t' P Q).1 ≫ pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))) =
              (L'.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))))
                ⟨P.1 ≫ pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂)))).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂)))) L₂ 𝓛₀ ∧
          LocIsoOnBase (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))))
            ((Scheme.Modules.pullback (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))))).obj ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj 𝓛))
            (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂)))) L₂)).obj 𝓛₀))) :
    (∃ (S₁ : Type u) (_ : CommRing S₁) (_ : Algebra S S₁),
      Module.FaithfullyFlat S S₁ ∧
      ∀ (L₁ : RelativeGroupLaw S₁ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))),
        (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S₁)) (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))),
            (L₁.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))) =
              (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))) L₁ 𝓛₀ ∧
          LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))).obj 𝓛)
            (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))) L₁)).obj 𝓛₀)) := by sorry
