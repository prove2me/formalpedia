-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_principalSqrt_of_kernelTrivial_of_locIsoOnBase
-- name    : AlgebraicGeometry.Polarisation.exists_faithfullyFlat_principalSqrt_of_kernelTrivial_of_locIsoOnBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/22ec9fa5-1ba7-514e-b57f-f0cb7b5c1596
-- title:
--   Fppf-local square root for a kernel-trivial invertible sheaf
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, $f : A \to \operatorname{Spec} S$ a morphism and $L$ a relative group law on $f$ (a functorial group structure, with multiplication, unit and inverse, on the sections $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $f$ over arbitrary $t : T \to \operatorname{Spec} S$, the multiplication being natural in $T$). Let $\mathcal L, \mathcal L_0$ be modules on $A$ with $\mathcal L_0$ invertible (every point of $A$ has an open neighbourhood $U$ on which the restriction of $\mathcal L_0$ is isomorphic to the unit module). Assume `KernelTrivial f L 𝓛₀`: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} S$ and every section $x$ of $f$ over $t$, if the pullback along `sliceAt f x` of the Mumford bundle $m^*\mathcal L_0 \otimes (\mathrm{pr}_1^*\mathcal L_0^\vee \otimes \mathrm{pr}_2^*\mathcal L_0^\vee)$ on $A \times_S A$ is isomorphic to the unit module locally over the base $\operatorname{Spec} R$ (i.e. after restriction to the preimages of the members of an open cover), then $x$ is the unit section. Assume also `LocIsoOnBase f 𝓛 (𝓛₀ ⊗ (negMor f L)^* 𝓛₀)`, where `negMor f L` is the morphism $A \to A$ underlying the $L$-inverse of the identity section: each point of $\operatorname{Spec} S$ has an open neighbourhood $U$ with $\mathcal L$ and $\mathcal L_0 \otimes [-1]^*\mathcal L_0$ isomorphic over $f^{-1}U$. The conclusion asserts the existence of a commutative ring $S'$ with an $S$-algebra structure making $S'$ faithfully flat over $S$, such that for every relative group law $L'$ on the second projection $A \times_S \operatorname{Spec} S' \to \operatorname{Spec} S'$ which is compatible with $L$, in the sense that for all $T$, all $t' : T \to \operatorname{Spec} S'$ and all sections $P, Q$ over $t'$ the first projection of $L'.\mathrm{mul}\,t'\,P\,Q$ equals the $L$-product over $t'$ followed by $\operatorname{Spec}$ of $S \to S'$ of the first projections of $P$ and $Q$, there is an invertible module $\mathcal L_0'$ on $A \times_S \operatorname{Spec} S'$ with `KernelTrivial` for $L'$ and with $\mathrm{pr}_1^*\mathcal L$ isomorphic to $\mathcal L_0' \otimes [-1]_{L'}^*\mathcal L_0'$ locally over $\operatorname{Spec} S'$.
--
--   This supplies, from an explicit principal square root $\mathcal L \cong \mathcal L_0 \otimes [-1]^*\mathcal L_0$ with $\mathcal L_0$ of trivial Mumford kernel, the faithfully flat local square-root clause in the definition of a canonical polarisation datum; the asserted faithfully flat extension need not be a proper extension of $S$. It is used in the Čerednik–Drinfeld part of the construction, in recognising a canonical polarisation on a fake elliptic curve from one on a base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_principalSqrt_of_kernelTrivial_of_locIsoOnBase.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_faithfullyFlat_principalSqrt_of_kernelTrivial_of_locIsoOnBase
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (𝓛 𝓛₀ : A.Modules) (h₀ : Scheme.Modules.IsInvertible 𝓛₀) (hK : KernelTrivial f L 𝓛₀)
    (hsq : LocIsoOnBase f 𝓛 (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₀)) :
    (∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S'),
      Module.FaithfullyFlat S S' ∧
      ∀ (L' : RelativeGroupLaw S' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
            (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
              (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S S')))).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L' 𝓛₀ ∧
          LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj 𝓛)
            (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L')).obj 𝓛₀)) := by sorry
