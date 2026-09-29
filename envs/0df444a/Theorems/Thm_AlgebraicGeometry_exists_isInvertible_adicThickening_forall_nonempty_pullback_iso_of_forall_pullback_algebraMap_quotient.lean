-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isInvertible_adicThickening_forall_nonempty_pullback_iso_of_forall_pullback_algebraMap_quotient
-- name    : AlgebraicGeometry.exists_isInvertible_adicThickening_forall_nonempty_pullback_iso_of_forall_pullback_algebraMap_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/72efcf6f-d20a-5679-8ec5-0602158c88a3
-- title:
--   Transporting compatible line bundles across adic thickenings
-- statement:
--   Let $S$ and $R$ be commutative rings with $R$ an $S$-algebra, let $I \subseteq R$ be an ideal, let $Y$ be a scheme and let $g \colon Y \to \operatorname{Spec} S$ be a morphism. Write $X'_k = Y \times_{\operatorname{Spec} S} \operatorname{Spec}(R/I^{k+1})$ and $X = Y \times_{\operatorname{Spec} S} \operatorname{Spec} R$, the fibre products being taken along $g$ and the morphisms induced by the structure maps. Assume given, for every $k \in \mathbb{N}$, morphisms $j_k \colon X'_k \to X$ compatible with the first projections to $Y$ and with the second projections up to $\operatorname{Spec}$ of the quotient map $R \to R/I^{k+1}$, and morphisms $t_k \colon X'_k \to X'_{k+1}$ compatible with the first projections to $Y$ and satisfying $j_{k+1} \circ t_k = j_k$ (no condition is imposed on the second projection of $t_k$). Assume further given modules $\mathcal{L}_k$ on $X'_k$, each invertible in the sense that every point has an open neighbourhood $U$ over which the restriction of $\mathcal{L}_k$ along $U \hookrightarrow X'_k$ admits an isomorphism to the unit module of $U$, and such that for every $k$ there exists an isomorphism $t_k^{*}\mathcal{L}_{k+1} \cong \mathcal{L}_k$. Then there exists a family of modules $L_n$ on the adic thickenings $\operatorname{adicThickening}$ of $X$ along $I$, that is on $X \times_{\operatorname{Spec} R} \operatorname{Spec}(R/I^{n+1})$ formed with the second projection $X \to \operatorname{Spec} R$, such that each $L_n$ is invertible in the above local sense, for each $n$ there exists an isomorphism between the pullback of $L_{n+1}$ along `adicThickeningTransition` and $L_n$, and moreover for every module $M$ on $X$: if for every $n$ the pullback of $M$ along the structural morphism `adicThickeningι` of the $n$-th thickening into $X$ admits an isomorphism to $L_n$, then for every $k$ the pullback $j_k^{*}M$ admits an isomorphism to $\mathcal{L}_k$. All isomorphisms are asserted as nonemptiness of the relevant type of isomorphisms, no choice of isomorphism being part of the data.
--
--   This is the comparison bridge between the two descriptions of the infinitesimal neighbourhoods of the locus cut out by $I$ on $Y \times_{\operatorname{Spec} S} \operatorname{Spec} R$, obtained from the pasting law for fibre products: a compatible system of line bundles on the thickenings $Y \times_S \operatorname{Spec}(R/I^{k+1})$ yields one on the adic thickenings, and any module on $X$ algebraising the latter also restricts back to the original system. It is used in the fake elliptic curve constructions of Cerednik–Drinfeld type, where formal algebraisation is applied to the adic thickenings of a relative curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isInvertible_adicThickening_forall_nonempty_pullback_iso_of_forall_pullback_algebraMap_quotient.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_AdicThickening

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isInvertible_adicThickening_forall_nonempty_pullback_iso_of_forall_pullback_algebraMap_quotient
    {S R : Type u} [CommRing S] [CommRing R] [Algebra S R] (I : Ideal R)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of S))

    (j : ∀ k : ℕ, pullback g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1))))) ⟶
      pullback g (Spec.map (CommRingCat.ofHom (algebraMap S R))))
    (hj₁ : ∀ k, j k ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
      pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1))))))
    (hj₂ : ∀ k, j k ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
      pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1))))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (k + 1)))))
    (t : ∀ k : ℕ, pullback g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1))))) ⟶
      pullback g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1 + 1))))))
    (ht₁ : ∀ k, t k ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1 + 1))))) =
      pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1))))))
    (ht : ∀ k, t k ≫ j (k + 1) = j k)

    (𝓛k : ∀ k : ℕ, (pullback g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1)))))).Modules)
    (hinv : ∀ k, Scheme.Modules.IsInvertible (𝓛k k))
    (hcompat : ∀ k : ℕ, Nonempty ((Scheme.Modules.pullback (t k)).obj (𝓛k (k + 1)) ≅ 𝓛k k)) :
    ∃ L : ∀ n : ℕ, (adicThickening (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S R)))) I n).Modules,
      (∀ n, Scheme.Modules.IsInvertible (L n)) ∧
      (∀ n, Nonempty ((Scheme.Modules.pullback
        (adicThickeningTransition (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S R)))) I n)).obj
          (L (n + 1)) ≅ L n)) ∧
      ∀ M : (pullback g (Spec.map (CommRingCat.ofHom (algebraMap S R)))).Modules,
        (∀ n, Nonempty ((Scheme.Modules.pullback
          (adicThickeningι (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S R)))) I n)).obj M ≅ L n)) →
        ∀ k : ℕ, Nonempty ((Scheme.Modules.pullback (j k)).obj M ≅ 𝓛k k) := by sorry
