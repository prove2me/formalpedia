-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_principalRoot_over_of_ringHom_of_forall_exists_principalRoot
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_principalRoot_over_of_ringHom_of_forall_exists_principalRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/cb5b3638-af40-5851-94df-8d9a57fb8382
-- title:
--   Principal-root data base-change along a point of the covering algebra
-- statement:
--   Let $u$ be a polarised abelian scheme of the project's type, with parameters $g,d,n$, over a commutative ring $S$: in particular it carries a structure morphism $u.f : A \to \operatorname{Spec} S$, a relative group law $u.L$ and an invertible module $u.\mathrm{pol}$ on $A$. Let $S'$ be an $S$-algebra, and write $A' \to \operatorname{Spec} S'$ for the second projection of the fibre product of $u.f$ with $\operatorname{Spec}$ of $S \to S'$. The hypothesis is that for every relative group law $L'$ on $A' \to \operatorname{Spec} S'$ whose multiplication is compatible with $u.L$ under the first projection $A' \to A$ (on points $P,Q$ of $A'$ over any $T \to \operatorname{Spec} S'$), there are an invertible module $\mathcal L_0$ on $A'$ and naturals $a,b$ with $a+b \ge 1$ such that $\mathcal L_0$ has trivial kernel for $L'$ — i.e. any point $x$ over any $\operatorname{Spec} R \to \operatorname{Spec} S'$ whose slice of the Mumford bundle $m^*\mathcal L_0 \otimes \mathrm{pr}_1^*\mathcal L_0^\vee \otimes \mathrm{pr}_2^*\mathcal L_0^\vee$ is, over some open neighbourhood of each base point, isomorphic to the unit, equals the identity section — and such that the pullback of $u.\mathrm{pol}$ to $A'$ and $\mathcal L_0^{\otimes a} \otimes (\iota^*\mathcal L_0)^{\otimes b}$, with $\iota$ the inversion morphism of $L'$, become isomorphic over the preimage of some open neighbourhood of each point of $\operatorname{Spec} S'$. Then, for every commutative ring $R$, ring homomorphism $\chi : S' \to R$ and morphism $t_R : \operatorname{Spec} R \to \operatorname{Spec} S$ factoring as $\operatorname{Spec} \chi$ followed by $\operatorname{Spec}$ of $S \to S'$, the same package exists over $t_R$: a relative group law $L_R$ on the second projection $A_R \to \operatorname{Spec} R$ compatible with $u.L$ under the first projection $A_R \to A$ in the same sense, together with an invertible $\mathcal L_{0,R}$ on $A_R$ and naturals $a,b$ with $a+b \ge 1$ such that $\mathcal L_{0,R}$ has trivial kernel for $L_R$ and the pullback of $u.\mathrm{pol}$ to $A_R$ is locally isomorphic on the base to $\mathcal L_{0,R}^{\otimes a} \otimes (\iota_R^*\mathcal L_{0,R})^{\otimes b}$.
--
--   This is the base-change step for the data of a principal (Mumford-theoretic) root of a polarisation: the existence of a kernel-trivial invertible module whose symmetric tensor combination recovers the polarisation descends from an auxiliary algebra $S'$ to any ring $R$ receiving $S'$, the group law being transported by base change. It is used in the construction of such roots over algebraically closed fields together with the associated theta point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_principalRoot_over_of_ringHom_of_forall_exists_principalRoot.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_principalRoot_over_of_ringHom_of_forall_exists_principalRoot
    {g d n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    (S' : Type) [CommRing S'] [Algebra S S']
    (hroot : ∀ (L' : RelativeGroupLaw S' (pullback.snd u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S'))
          (P Q : SchemeHomOver t' (pullback.snd u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
          (L'.mul t' P Q).1 ≫ pullback.fst u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
            (u.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
              ⟨P.1 ≫ pullback.fst u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
      ∃ (𝓛₀ : (pullback u.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))).Modules) (a b : ℕ),
        1 ≤ a + b ∧ Scheme.Modules.IsInvertible 𝓛₀ ∧
        Polarisation.KernelTrivial (pullback.snd u.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L' 𝓛₀ ∧
        Polarisation.LocIsoOnBase (pullback.snd u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
          ((Scheme.Modules.pullback (pullback.fst u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj u.pol)
          (Scheme.Modules.tpow 𝓛₀ a ⊗
            Scheme.Modules.tpow ((Scheme.Modules.pullback
              (Polarisation.negMor (pullback.snd u.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L')).obj 𝓛₀) b))
    {R : Type} [CommRing R] (χ : S' →+* R) (tR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (htR : Spec.map (CommRingCat.ofHom χ) ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')) = tR) :
    ∃ (LR : RelativeGroupLaw R (pullback.snd u.f tR))
      (_ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of R))
          (P Q : SchemeHomOver t' (pullback.snd u.f tR)),
          (LR.mul t' P Q).1 ≫ pullback.fst u.f tR =
            (u.L.mul (t' ≫ tR)
              ⟨P.1 ≫ pullback.fst u.f tR, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst u.f tR, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
      (𝓛₀ : (pullback u.f tR).Modules) (a b : ℕ),
      1 ≤ a + b ∧ Scheme.Modules.IsInvertible 𝓛₀ ∧
      Polarisation.KernelTrivial (pullback.snd u.f tR) LR 𝓛₀ ∧
      Polarisation.LocIsoOnBase (pullback.snd u.f tR)
        ((Scheme.Modules.pullback (pullback.fst u.f tR)).obj u.pol)
        (Scheme.Modules.tpow 𝓛₀ a ⊗ Scheme.Modules.tpow ((Scheme.Modules.pullback (Polarisation.negMor (pullback.snd u.f tR) LR)).obj 𝓛₀) b) := by sorry
