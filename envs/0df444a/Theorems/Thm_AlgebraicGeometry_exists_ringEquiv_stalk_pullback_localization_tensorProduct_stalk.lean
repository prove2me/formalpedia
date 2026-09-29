-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk
-- name    : AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/7d7a1340-ba8d-5a29-a212-6383ef225ffc
-- title:
--   Stalks of a base change as localisations of mathcal O_{X,z} ⊗_A k
-- statement:
--   Let $A$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} A$ a morphism of schemes, and $k$ a commutative ring equipped with an $A$-algebra structure, so that $\operatorname{Spec}$ of the structure map gives a morphism $\operatorname{Spec} k \to \operatorname{Spec} A$. Let $x$ be a point of the fibre product $P = X \times_{\operatorname{Spec} A} \operatorname{Spec} k$ and let $z$ be its image under the first projection $\mathrm{pr}_1 : P \to X$. The stalk $\mathcal O_{X,z}$ is viewed as an $A$-algebra via the composite of the inverse of the isomorphism $A \cong \Gamma(\operatorname{Spec} A, \mathcal O)$, the map on global sections induced by $f$, and the germ map at $z$ from sections over the whole of $X$. The assertion is that there exist a prime ideal $\mathfrak q$ of $\mathcal O_{X,z} \otimes_A k$ and a ring isomorphism $e : \mathcal O_{P,x} \xrightarrow{\ \sim\ } (\mathcal O_{X,z} \otimes_A k)_{\mathfrak q}$ such that, first, the contraction of $\mathfrak q$ along $s \mapsto s \otimes 1$ is exactly the maximal ideal of the local ring $\mathcal O_{X,z}$, and second, for every $s \in \mathcal O_{X,z}$ the image under $e$ of the stalk map of $\mathrm{pr}_1$ at $x$ applied to $s$ equals the image of $s \otimes 1$ under the localisation map.
--
--   This is the standard local description of a base change: the local ring of $X \times_{\operatorname{Spec} A} \operatorname{Spec} k$ at a point is a localisation of $\mathcal O_{X,z} \otimes_A k$ at a prime lying over the maximal ideal of $\mathcal O_{X,z}$, compatibly with the stalk map of the projection. It is used in the local study of the fibres of the model of $X_1(p)$ over $\mathbb Z$, for identifying irreducible components, detecting non-regular points, and bounding Krull dimensions of stalks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk
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
      ∀ s : X.presheaf.stalk z,
        e (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).stalkMap x).hom s) =
          algebraMap ((X.presheaf.stalk z) ⊗[A] k) (Localization.AtPrime 𝔮) (s ⊗ₜ[A] 1) := by sorry
