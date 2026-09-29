-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd
-- name    : AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/b35ac024-8c75-5ae2-9eca-94baba74daf6
-- title:
--   Stalks of a base change as localisations of 𝒪_{X,z}⊗_A k
-- statement:
--   Let $A$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} A$ a morphism, and $k$ a commutative ring equipped with an $A$-algebra structure; form the fibre product of $f$ with $\operatorname{Spec}$ of the structure morphism $A \to k$, and let $x$ be a point of it. Write $z$ for the image of $x$ under the base map of the first projection, and give the stalk $\mathcal{O}_{X,z}$ the $A$-algebra structure obtained by composing the inverse of the global-sections comparison isomorphism $\Gamma(\operatorname{Spec} A) \cong A$, the map $f$ induces on global sections, and the germ map at $z$ on the top open. The assertion is that there exist a prime ideal $\mathfrak{q}$ of $\mathcal{O}_{X,z} \otimes_A k$ and a ring isomorphism $e$ from the stalk of the fibre product at $x$ onto the localisation of $\mathcal{O}_{X,z} \otimes_A k$ at $\mathfrak{q}$ such that: the contraction of $\mathfrak{q}$ along $s \mapsto s \otimes 1$ is the maximal ideal of the local ring $\mathcal{O}_{X,z}$; $e$ carries the image of any $s \in \mathcal{O}_{X,z}$ under the stalk map of the first projection at $x$ to the image of $s \otimes 1$ in the localisation; and $e$ carries the germ at $x$ of the global section of the fibre product obtained from $c \in k$ by the comparison isomorphism $\Gamma(\operatorname{Spec} k) \cong k$ followed by the second projection to the image of $1 \otimes c$.
--
--   This is the standard description of the local rings of a base change $X \times_{\operatorname{Spec} A} \operatorname{Spec} k$ as localisations of $\mathcal{O}_{X,z} \otimes_A k$, here in a form recording compatibility with both projections, so that the germs coming from $X$ and the scalars coming from $k$ are identified with $s \otimes 1$ and $1 \otimes c$ respectively. It is used in the curve-theoretic part of the argument, where local rings of base-changed curves are analysed through their completions and through the prime ideals lying over the maximal ideal of $\mathcal{O}_{X,z}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd
    {A : Type u} [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A))
    (k : Type u) [CommRing k] [Algebra A k]
    (x : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap A k))))) :
    letI z := (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base x
    letI : Algebra A (X.presheaf.stalk z) :=
      ((X.presheaf.germ ⊤ z trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).toAlgebra
    ∃ (𝔮 : Ideal ((X.presheaf.stalk z) ⊗[A] k)) (_ : 𝔮.IsPrime)
      (e : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).presheaf.stalk x ≃+* Localization.AtPrime 𝔮),
      𝔮.comap (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := X.presheaf.stalk z) (B := k)).toRingHom =
        IsLocalRing.maximalIdeal (X.presheaf.stalk z) ∧
      (∀ s : X.presheaf.stalk z,
        e (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).stalkMap x).hom s) =
          algebraMap ((X.presheaf.stalk z) ⊗[A] k) (Localization.AtPrime 𝔮) (s ⊗ₜ[A] 1)) ∧
      (∀ c : k,
        e ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).presheaf.germ ⊤ x trivial
            ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))) =
          algebraMap ((X.presheaf.stalk z) ⊗[A] k) (Localization.AtPrime 𝔮) (1 ⊗ₜ[A] c)) := by sorry
