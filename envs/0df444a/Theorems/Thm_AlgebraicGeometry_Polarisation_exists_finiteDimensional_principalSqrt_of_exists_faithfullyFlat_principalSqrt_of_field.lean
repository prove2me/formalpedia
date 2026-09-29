-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_finiteDimensional_principalSqrt_of_exists_faithfullyFlat_principalSqrt_of_field
-- name    : AlgebraicGeometry.Polarisation.exists_finiteDimensional_principalSqrt_of_exists_faithfullyFlat_principalSqrt_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/70c3ff91-cc02-54f9-8e63-0628adb3a668
-- title:
--   Principal square roots descend to a finite extension of k
-- statement:
--   Let $k$ be a field, $f : A \to \operatorname{Spec} k$ a morphism of schemes, and $L$ a relative group law on $f$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections over arbitrary $t : T \to \operatorname{Spec} k$, compatible with composition in $T$; assume $L$ is commutative and that $f$ satisfies `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ carries some relative group law. Let $\mathcal L$ be a module on $A$ that is invertible, i.e. locally on $A$ its restriction is isomorphic to the unit sheaf. Assume the following: there is a commutative $k$-algebra $S'$, faithfully flat as a $k$-module, such that for every relative group law $L'$ on the base change $A_{S'} \to \operatorname{Spec} S'$ whose multiplication is compatible with that of $L$ under the projection $A_{S'} \to A$ (on sections over any $t' : T \to \operatorname{Spec} S'$), there exists an invertible module $\mathcal L_0$ on $A_{S'}$ such that (i) `KernelTrivial` holds for $(L', \mathcal L_0)$: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} S'$ and every section $x$ over $t$, if the pullback of the Mumford bundle $m^{*}\mathcal L_0 \otimes \operatorname{pr}_1^{*}\mathcal L_0^{\vee} \otimes \operatorname{pr}_2^{*}\mathcal L_0^{\vee}$ along the slice at $x$ is, locally over points of $\operatorname{Spec} R$, isomorphic to the unit module, then $x$ is the identity section; and (ii) the pullback of $\mathcal L$ to $A_{S'}$ and $\mathcal L_0 \otimes [-1]^{*}\mathcal L_0$ are, locally over points of $\operatorname{Spec} S'$, isomorphic, where $[-1]$ is the inversion morphism attached to $L'$. The conclusion is that the same statement holds with $S'$ replaced by a field: there exist a field $k'$ and a $k$-algebra structure on $k'$ with $k'/k$ finite-dimensional such that every relative group law on $A_{k'} \to \operatorname{Spec} k'$ compatible with $L$ in the above sense admits an invertible $\mathcal L_0$ satisfying (i) and (ii) over $k'$.
--
--   This is the field case of the descent of an fppf-local principal square root of $\mathcal L$ (a line bundle $\mathcal L_0$ with trivial kernel in the sense of Mumford's $\Lambda$-construction and with $\mathcal L \simeq \mathcal L_0 \otimes [-1]^{*}\mathcal L_0$ locally on the base) to a finite extension of the base field. It feeds the corresponding statement over a discrete valuation ring, used in assembling canonical polarisation data on abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_finiteDimensional_principalSqrt_of_exists_faithfullyFlat_principalSqrt_of_field.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_finiteDimensional_principalSqrt_of_exists_faithfullyFlat_principalSqrt_of_field
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hroot : (∃ (S' : Type) (_ : CommRing S') (_ : Algebra k S'),
      Module.FaithfullyFlat k S' ∧
      ∀ (L' : RelativeGroupLaw S' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k S'))))),
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k S'))))),
            (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k S'))) =
              (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap k S'))))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k S')))).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k S')))) L' 𝓛₀ ∧
          LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k S'))))
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k S'))))).obj 𝓛)
            (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k S')))) L')).obj 𝓛₀))) :
    ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
      ∀ (L' : RelativeGroupLaw k' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))),
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of k')) (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))),
            (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) =
              (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) L' 𝓛₀ ∧
          LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).obj 𝓛)
            (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) L')).obj 𝓛₀) := by sorry
