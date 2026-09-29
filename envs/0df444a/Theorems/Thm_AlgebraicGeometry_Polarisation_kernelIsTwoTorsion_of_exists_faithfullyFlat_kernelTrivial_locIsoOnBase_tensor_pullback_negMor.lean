-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_of_exists_faithfullyFlat_kernelTrivial_locIsoOnBase_tensor_pullback_negMor
-- name    : AlgebraicGeometry.Polarisation.kernelIsTwoTorsion_of_exists_faithfullyFlat_kernelTrivial_locIsoOnBase_tensor_pullback_negMor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/c72deda1-11aa-5507-907c-a64b69ccabc1
-- title:
--   K(L)=A[2] from a faithfully flat local square root
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism, $L$ a relative group law for $f$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of points over arbitrary $t : T \to \operatorname{Spec} S$, compatible with base change) which is commutative, and suppose the bundle of properties `AbelianSchemePropertyBundle` holds for $f$, i.e. $f$ is smooth and proper, each fibre of $f$ over a point of $\operatorname{Spec} S$ is connected, and $f$ admits a relative group law. Let $\mathcal L$ be an invertible module on $A$ (locally on $A$ isomorphic to the unit). Assume there are a commutative ring $S'$, an $S$-algebra structure on $S'$ making $S'$ faithfully flat over $S$, such that, writing $\iota : \operatorname{Spec} S' \to \operatorname{Spec} S$ for the induced morphism and $p_1, p_2$ for the projections of $A \times_{\operatorname{Spec} S} \operatorname{Spec} S'$, the following holds: for every relative group law $L'$ for $p_2$ whose multiplication is compatible with that of $L$ along $p_1$, in the sense that $(L'.\mathrm{mul}\, t'\, P\, Q)$ followed by $p_1$ equals $L.\mathrm{mul}\,(t' \circ \iota)$ applied to $P$ followed by $p_1$ and $Q$ followed by $p_1$, for all $t' : T \to \operatorname{Spec} S'$ and all points $P, Q$ over $t'$, there exists an invertible module $\mathcal L_0$ on $A \times_{\operatorname{Spec} S} \operatorname{Spec} S'$ such that $\mathcal L_0$ has trivial kernel for $L'$ — for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} S'$ and every point $x$ over $t$, if the pullback of the Mumford bundle $m^*\mathcal L_0 \otimes (p_1^*\mathcal L_0^\vee \otimes p_2^*\mathcal L_0^\vee)$ along the slice at $x$ is isomorphic to the unit after restriction to the preimage of some open neighbourhood of each point of $\operatorname{Spec} R$, then $x$ is the identity point — and such that the pullback of $\mathcal L$ along $p_1$ and $\mathcal L_0 \otimes [-1]^*\mathcal L_0$ (where $[-1]$ is `negMor` for $L'$, the inverse of the identity point) become isomorphic after restricting over a suitable open neighbourhood of each point of $\operatorname{Spec} S'$. The conclusion is that the kernel of $\mathcal L$ is the $2$-torsion: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} S$ and every point $x$ of $f$ over $t$, the pullback along the slice at $x$ of the Mumford bundle of $\mathcal L$ is locally on $\operatorname{Spec} R$ isomorphic to the unit if and only if $L.\mathrm{mul}\, t\, x\, x$ is the identity point.
--
--   This is the statement that an invertible module which, after a faithfully flat base change, admits a symmetric principal square root has kernel exactly the $2$-torsion subscheme, in the relative-point formulation used for abelian schemes. It is the step that produces the polarisation-kernel clause in the assembly of canonical polarisation data over a discrete valuation ring in the Čerednik–Drinfel'd setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_of_exists_faithfullyFlat_kernelTrivial_locIsoOnBase_tensor_pullback_negMor.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.kernelIsTwoTorsion_of_exists_faithfullyFlat_kernelTrivial_locIsoOnBase_tensor_pullback_negMor
    (S : Type) [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hroot : ∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S'),
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
            (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L')).obj 𝓛₀)) :
    KernelIsTwoTorsion f L 𝓛 := by sorry
