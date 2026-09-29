-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCanonicalPolData_exists_faithfullyFlat_sqrt_of_forall_away_of_isInvertible
-- name    : CerednikDrinfeld.QM.IsCanonicalPolData.exists_faithfullyFlat_sqrt_of_forall_away_of_isInvertible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/919896f2-9959-5616-80c4-cb34c82f385a
-- title:
--   Principal square root clause is local on the base
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, $f : A \to \operatorname{Spec} S$ a morphism and $L$ a relative group law on $f$, i.e. a functorial group structure on the sets of sections $\{\varphi : T \to A \mid \varphi \circ f = t\}$ for $S$-schemes $t : T \to \operatorname{Spec} S$. Let $r : \mathrm{Fin}\,k \to S$ generate the unit ideal, and for each $i$ let $f' i : A'_i \to \operatorname{Spec} S[1/r_i]$ together with $g_i : A'_i \to A$ exhibit $A'_i$ as the pullback of $f$ along $\operatorname{Spec} S[1/r_i] \to \operatorname{Spec} S$, and let $L'_i$ be a relative group law on $f' i$ whose multiplication is carried by $g_i$ to that of $L$. Let $\mathcal L$ be a module on $A$ that is invertible (every point of $A$ has a neighbourhood on which $\mathcal L$ restricts to the unit sheaf). Assume for each $i$: there is a faithfully flat $S[1/r_i]$-algebra $S'_i$ such that for every relative group law $L''$ on the second projection $A'_i \times_{\operatorname{Spec} S[1/r_i]} \operatorname{Spec} S'_i \to \operatorname{Spec} S'_i$ compatible, via the first projection, with $L'_i$, there is an invertible module $\mathcal L_0$ on that pullback with `KernelTrivial` for $L''$ (every section whose slice of the associated Mumford bundle is trivial locally on the base is the identity section) and with the pullback of $g_i^{*}\mathcal L$ isomorphic to $\mathcal L_0 \otimes [-1]^{*}\mathcal L_0$ locally on $\operatorname{Spec} S'_i$, where $[-1]$ is the inversion morphism of $L''$. The conclusion is the same assertion for $f$, $L$, $\mathcal L$ over $S$: there exists a faithfully flat $S$-algebra $S'$ such that for every relative group law on $A \times_{\operatorname{Spec} S} \operatorname{Spec} S' \to \operatorname{Spec} S'$ compatible with $L$ there is an invertible $\mathcal L_0$ with trivial kernel whose tensor product with its pullback along inversion is, locally on $\operatorname{Spec} S'$, isomorphic to the pullback of $\mathcal L$.
--
--   This is the descent step for the clause of [`CerednikDrinfeld.QM.IsCanonicalPolData`](def/CerednikDrinfeld_QMCanonicalPol.html#L15) asserting that, after a faithfully flat base change, the bundle $\mathcal L$ acquires a square root $\mathcal L_0$ with trivial kernel in the sense of $\mathcal L \cong \mathcal L_0 \otimes [-1]^{*}\mathcal L_0$; the clause is shown to be local on the base for a cover of $\operatorname{Spec} S$ by the basic opens $\operatorname{Spec} S[1/r_i]$. It feeds [`CerednikDrinfeld.QM.IsCanonicalPolData.of_forall_away`](thm.html#CerednikDrinfeld.QM.IsCanonicalPolData.of_forall_away), the statement that being a canonical polarisation datum is a Zariski-local property of the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCanonicalPolData_exists_faithfullyFlat_sqrt_of_forall_away_of_isInvertible.lean

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

universe u v

theorem CerednikDrinfeld.QM.IsCanonicalPolData.exists_faithfullyFlat_sqrt_of_forall_away_of_isInvertible
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (A' : Fin k → Scheme.{u}) (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (Localization.Away (r i))))
    (g : ∀ i, A' i ⟶ A)
    (hg : ∀ i, IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))))
    (L' : ∀ i, RelativeGroupLaw (Localization.Away (r i)) (f' i))
    (hL' : ∀ (i : Fin k) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of (Localization.Away (r i))))
      (x y : SchemeHomOver t' (f' i)),
      ((L' i).mul t' x y).1 ≫ g i =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))))
          ⟨x.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, y.2]⟩).1)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hloc : ∀ i, (∃ (S' : Type u) (_ : CommRing S') (_ : Algebra (Localization.Away (r i)) S'),
        Module.FaithfullyFlat (Localization.Away (r i)) S' ∧
        ∀ (L'' : RelativeGroupLaw S' (pullback.snd (f' i) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (r i)) S'))))),
          (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' (pullback.snd (f' i) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (r i)) S'))))),
              (L''.mul t' P Q).1 ≫ pullback.fst (f' i) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (r i)) S'))) =
                ((L' i).mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (r i)) S'))))
                  ⟨P.1 ≫ pullback.fst (f' i) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (r i)) S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst (f' i) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (r i)) S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∃ 𝓛₀ : (pullback (f' i) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (r i)) S')))).Modules,
            Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (pullback.snd (f' i) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (r i)) S')))) L'' 𝓛₀ ∧
            LocIsoOnBase (pullback.snd (f' i) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (r i)) S'))))
              ((Scheme.Modules.pullback (pullback.fst (f' i) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (r i)) S'))))).obj ((Scheme.Modules.pullback (g i)).obj 𝓛))
              (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd (f' i) (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (r i)) S')))) L'')).obj 𝓛₀))) :
    (∃ (S' : Type u) (_ : CommRing S') (_ : Algebra S S'),
      Module.FaithfullyFlat S S' ∧
      ∀ (L'' : RelativeGroupLaw S' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
        (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
            (L''.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
              (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S S')))).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L'' 𝓛₀ ∧
          LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj 𝓛)
            (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L'')).obj 𝓛₀)) := by sorry
