-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_intermediateField_isGalois_galois_twist_comp_pullback_map_eq
-- name    : AlgebraicGeometry.exists_intermediateField_isGalois_galois_twist_comp_pullback_map_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/7652bf6d-3ee3-51df-8ad5-e103a176175b
-- title:
--   Descent of a Galois-equivariant morphism to a finite Galois level
-- statement:
--   Let $k \subseteq K$ be fields with $K/k$ Galois, let $X, Y$ be schemes with structure morphisms $f_X : X \to \operatorname{Spec} k$ and $f_Y : Y \to \operatorname{Spec} k$, where the space of $X$ is compact and quasi-separated and $f_Y$ is separated and locally of finite type. Let $f$ be a morphism from the pullback of $f_X$ along $\operatorname{Spec}$ of $k \to K$ to the pullback of $f_Y$ along the same morphism, compatible with the second projections in the sense that $f$ followed by the second projection of the $Y$-pullback is the second projection of the $X$-pullback, and assume that for every $\sigma \in \operatorname{Aut}(K/k)$ satisfying $\operatorname{Spec}\sigma$ followed by $\operatorname{Spec}(k \to K)$ equal to $\operatorname{Spec}(k \to K)$, the twist $\mathrm{id}_X \times \operatorname{Spec}\sigma$ followed by $f$ equals $f$ followed by $\mathrm{id}_Y \times \operatorname{Spec}\sigma$. Then there exist an intermediate field $L$ of $K/k$ that is finite-dimensional and Galois over $k$, a morphism $g$ from the pullback of $f_X$ along $\operatorname{Spec}(k \to L)$ to the pullback of $f_Y$ along $\operatorname{Spec}(k \to L)$, and the identity $\operatorname{Spec}(L \to K)$ followed by $\operatorname{Spec}(k \to L)$ equal to $\operatorname{Spec}(k \to L\!\to\!K)$ as $\operatorname{Spec}(k \to K)$, such that: $g$ is compatible with the second projections; for every $\tau \in \operatorname{Aut}(L/k)$ with $\operatorname{Spec}\tau$ followed by $\operatorname{Spec}(k \to L)$ equal to $\operatorname{Spec}(k \to L)$, the twist $\mathrm{id}_X \times \operatorname{Spec}\tau$ followed by $g$ equals $g$ followed by $\mathrm{id}_Y \times \operatorname{Spec}\tau$; and the square commutes, namely $f$ followed by the projection $\mathrm{id}_Y \times \operatorname{Spec}(L \to K)$ onto the $L$-pullback of $f_Y$ equals the projection $\mathrm{id}_X \times \operatorname{Spec}(L \to K)$ followed by $g$.
--
--   This is the finite-level step in Galois descent of morphisms of schemes: a morphism after base change to a possibly infinite Galois extension, commuting with all Galois twists, already arises from a twist-equivariant morphism over a finite Galois subextension. It combines the standard limit argument descending a morphism to a finite subextension with passage to the normal closure, and it feeds the descent statement [`AlgebraicGeometry.exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq`](thm.html#AlgebraicGeometry.exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq); separatedness of $f_Y$ enters through [`AlgebraicGeometry.eq_of_pullback_map_eq_pullback_map_of_isSeparated`](thm.html#AlgebraicGeometry.eq_of_pullback_map_eq_pullback_map_of_isSeparated), which makes the twist-equivariance at level $L$ checkable after base change to $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_intermediateField_isGalois_galois_twist_comp_pullback_map_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_intermediateField_isGalois_galois_twist_comp_pullback_map_eq
    (k K : Type) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (X Y : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] [IsSeparated fY] [LocallyOfFiniteType fY]
    (f : pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ pullback fY (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hf : f ≫ pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hgal : ∀ (σ : K ≃ₐ[k] K)
      (hσ : Spec.map (CommRingCat.ofHom ((σ : K →ₐ[k] K) : K →+* K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
        Spec.map (CommRingCat.ofHom (algebraMap k K))),
      pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          (𝟙 X) (Spec.map (CommRingCat.ofHom ((σ : K →ₐ[k] K) : K →+* K))) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hσ]) ≫ f =
        f ≫ pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          (𝟙 Y) (Spec.map (CommRingCat.ofHom ((σ : K →ₐ[k] K) : K →+* K))) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hσ])) :
    ∃ (L : IntermediateField k K) (_ : FiniteDimensional k L) (_ : IsGalois k L)
      (g : pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶ pullback fY (Spec.map (CommRingCat.ofHom (algebraMap k L))))
      (hι : Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
        Spec.map (CommRingCat.ofHom (algebraMap k K))),
      g ≫ pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
        pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) ∧
      (∀ (τ : L ≃ₐ[k] L)
        (hτ : Spec.map (CommRingCat.ofHom ((τ : L →ₐ[k] L) : L →+* L)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
          Spec.map (CommRingCat.ofHom (algebraMap k L))),
        pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) fX (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 X) (Spec.map (CommRingCat.ofHom ((τ : L →ₐ[k] L) : L →+* L))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hτ]) ≫ g =
          g ≫ pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) fY (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 Y) (Spec.map (CommRingCat.ofHom ((τ : L →ₐ[k] L) : L →+* L))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hτ])) ∧
      f ≫ pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 Y) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) =
        pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 X) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) ≫ g := by sorry
