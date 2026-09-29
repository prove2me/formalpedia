-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_kernelTrivial_locIsoOnBase_tensor_pullback_negMor_of_commRing
-- name    : AlgebraicGeometry.Polarisation.exists_faithfullyFlat_kernelTrivial_locIsoOnBase_tensor_pullback_negMor_of_commRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/5897b499-7e67-5362-a164-5e15b83c208c
-- title:
--   Principal square root of a symmetrised bundle, trivial cover
-- statement:
--   Let $S$ be a commutative ring, let $f\colon A \to \operatorname{Spec} S$ be a morphism of schemes, let $L$ be a relative group law on $f$ (a functorial group structure, with multiplication, unit and inversion natural in the base point, on the sets $\{\varphi\colon T \to A \mid \varphi \circ f = t\}$ of $A$-points over $t\colon T \to \operatorname{Spec} S$), and let $\mathcal L_0$ be a module on $A$ which is invertible, i.e. each point of $A$ has an open neighbourhood over which $\mathcal L_0$ pulls back to the unit module. Assume `KernelTrivial f L 𝓛₀`: for every commutative ring $R$, every $t\colon \operatorname{Spec} R \to \operatorname{Spec} S$ and every $A$-point $x$ over $t$, if the pullback along the slice $\mathrm{id} \times x$ of the Mumford bundle $m^*\mathcal L_0 \otimes (p_1^*\mathcal L_0^\vee \otimes p_2^*\mathcal L_0^\vee)$ on $A\times_S A$ is, locally on $\operatorname{Spec} R$, isomorphic to the unit module, then $x$ is the unit point. The assertion is: there exist a commutative ring $S'$ and an $S$-algebra structure on it making $S'$ a faithfully flat $S$-module such that, for every relative group law $L'$ on the projection $A' := A\times_S \operatorname{Spec} S' \to \operatorname{Spec} S'$ whose multiplication is compatible with that of $L$ through the first projection $p_1$ (for all $T$, all $t'\colon T \to \operatorname{Spec} S'$ and all $A'$-points $P,Q$ over $t'$, the composite of $L'$-product with $p_1$ is the $L$-product of the composites), there is an invertible module $\mathcal L_1$ on $A'$ with trivial Mumford kernel in the above sense for $L'$, and such that $p_1^*(\mathcal L_0 \otimes [-1]^*\mathcal L_0)$ and $\mathcal L_1 \otimes [-1]'^*\mathcal L_1$ become isomorphic over the preimage of some open neighbourhood of each point of $\operatorname{Spec} S'$; here $[-1]$ and $[-1]'$ denote the inversion morphisms $A\to A$, $A'\to A'$ attached to $L$ and $L'$.
--
--   This is the clause asserting that the symmetrisation $\mathcal L_0 \otimes [-1]^*\mathcal L_0$ of a principal invertible sheaf admits, flat-locally on the base, a principal square root, stated over an arbitrary commutative base ring rather than a field. It feeds the verification that such a symmetrisation constitutes a canonical polarisation datum, used in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_kernelTrivial_locIsoOnBase_tensor_pullback_negMor_of_commRing.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_faithfullyFlat_kernelTrivial_locIsoOnBase_tensor_pullback_negMor_of_commRing
    (S : Type) [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (𝓛₀ : A.Modules) (h₀ : Scheme.Modules.IsInvertible 𝓛₀) (hK : KernelTrivial f L 𝓛₀) :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S'),
      Module.FaithfullyFlat S S' ∧
      ∀ (L' : RelativeGroupLaw S' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
            (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
              (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₁ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S S')))).Modules,
          Scheme.Modules.IsInvertible 𝓛₁ ∧ KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L' 𝓛₁ ∧
          LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj
              (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₀))
            (𝓛₁ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L')).obj 𝓛₁) := by sorry
