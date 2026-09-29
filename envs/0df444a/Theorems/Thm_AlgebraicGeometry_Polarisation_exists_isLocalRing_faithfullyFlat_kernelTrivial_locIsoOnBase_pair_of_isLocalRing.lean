-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_isLocalRing_faithfullyFlat_kernelTrivial_locIsoOnBase_pair_of_isLocalRing
-- name    : AlgebraicGeometry.Polarisation.exists_isLocalRing_faithfullyFlat_kernelTrivial_locIsoOnBase_pair_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/09ff015c-8e9a-5153-bcd9-d0089c216ccc
-- title:
--   Common local faithfully flat cover carrying both square roots
-- statement:
--   Let $S$ be a local commutative ring, let $f : A \to \operatorname{Spec} S$ be a morphism of schemes and let $L$ be a relative group law on $f$ (functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of points over arbitrary $t : T \to \operatorname{Spec} S$, natural in $T$), and let $\mathcal L, \mathcal L'$ be modules on $A$. Assume, for each of $\mathcal L$ and $\mathcal L'$ separately, that there is a faithfully flat $S$-algebra $S'$ such that for every relative group law $L'$ on the projection $A \times_{\operatorname{Spec} S} \operatorname{Spec} S' \to \operatorname{Spec} S'$ that is compatible with $L$ along the other projection (the underlying morphism of $L'.\mathrm{mul}\,t'\,P\,Q$ composed with the first projection equals that of the $L$-product of the composites of $P$ and $Q$ with the first projection), there is a module $\mathcal L_0$ on $A \times_{\operatorname{Spec} S} \operatorname{Spec} S'$ which is invertible (locally on the total space isomorphic to the unit sheaf of modules), satisfies `KernelTrivial` for $L'$ — for every ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} S'$ and every point $x$ over $t$, triviality on the base of the slice at $x$ of the Mumford bundle of $\mathcal L_0$ forces $x$ to be the identity point — and such that the pullback of $\mathcal L$ (resp. $\mathcal L'$) along the first projection and $\mathcal L_0 \otimes [-1]^{*}\mathcal L_0$ are `LocIsoOnBase`, i.e. their restrictions over the preimage of some open neighbourhood of each point of $\operatorname{Spec} S'$ are isomorphic; here $[-1]$ is the morphism underlying the $L'$-inverse of the identity point. The conclusion is the existence of a single faithfully flat $S$-algebra $S''$ which is again a local ring, such that for every scheme $A''$, every $f'' : A'' \to \operatorname{Spec} S''$ and $g : A'' \to A$ forming a pullback square over $\operatorname{Spec} S'' \to \operatorname{Spec} S$, and every relative group law $L''$ on $f''$ for which $g$ is compatible with $L$ in the above sense, there exist modules $\mathcal L_0, \mathcal L_0'$ on $A''$, both invertible, both `KernelTrivial` for $f''$ and $L''$, with $g^{*}\mathcal L$ and $\mathcal L_0 \otimes [-1]^{*}\mathcal L_0$, and $g^{*}\mathcal L'$ and $\mathcal L_0' \otimes [-1]^{*}\mathcal L_0'$, `LocIsoOnBase` over $\operatorname{Spec} S''$, where $[-1]$ is now the inversion morphism attached to $L''$.
--
--   This amalgamates two separate faithfully flat covers, each supplying a principal square root of one of the two line bundles, into one faithfully flat cover whose base is still local and which carries both square roots simultaneously, and it does so for an arbitrary model $A''$ of the base change rather than only the chosen fibre product. It is the step that makes the comparison of two canonical polarisation data over a local base possible, and is used in [`CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_isLocalRing_of_isUnit_two`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_isLocalRing_of_isUnit_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_isLocalRing_faithfullyFlat_kernelTrivial_locIsoOnBase_pair_of_isLocalRing.lean

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_isLocalRing_faithfullyFlat_kernelTrivial_locIsoOnBase_pair_of_isLocalRing
    {S : Type} [CommRing S] [IsLocalRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (𝓛 𝓛' : A.Modules)
    (h : (∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S'),
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
            (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L')).obj 𝓛₀)))
    (h' : (∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S'),
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
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj 𝓛')
            (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L')).obj 𝓛₀))) :
    ∃ (S'' : Type) (_ : CommRing S'') (_ : Algebra S S''),
      IsLocalRing S'' ∧ Module.FaithfullyFlat S S'' ∧
      ∀ (A'' : Scheme.{0}) (f'' : A'' ⟶ Spec (CommRingCat.of S'')) (g : A'' ⟶ A)
        (hg : IsPullback g f'' f (Spec.map (CommRingCat.ofHom (algebraMap S S'')))) (L'' : RelativeGroupLaw S'' f''),
        (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S'')) (P Q : SchemeHomOver t' f''),
            (L''.mul t' P Q).1 ≫ g =
              (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S'')))
                ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ 𝓛₀' : A''.Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧ Scheme.Modules.IsInvertible 𝓛₀' ∧
          KernelTrivial f'' L'' 𝓛₀ ∧ KernelTrivial f'' L'' 𝓛₀' ∧
          LocIsoOnBase f'' ((Scheme.Modules.pullback g).obj 𝓛) (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor f'' L'')).obj 𝓛₀) ∧
          LocIsoOnBase f'' ((Scheme.Modules.pullback g).obj 𝓛') (𝓛₀' ⊗ (Scheme.Modules.pullback (negMor f'' L'')).obj 𝓛₀') := by sorry
