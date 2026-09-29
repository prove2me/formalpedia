-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq
-- name    : AlgebraicGeometry.exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/45031e61-5192-5b1e-adb3-af883c700eda
-- title:
--   Galois descent of morphisms between base-changed k-schemes
-- statement:
--   Let $k \subseteq K$ be fields with $K$ a $k$-algebra such that $K/k$ is Galois (no finiteness of the degree is assumed), and let $X, Y$ be schemes equipped with morphisms $f_X : X \to \operatorname{Spec} k$ and $f_Y : Y \to \operatorname{Spec} k$, where the underlying space of $X$ is quasi-compact and quasi-separated and $f_Y$ is separated and locally of finite type. Let $f$ be a morphism from the fibre product of $f_X$ with $\operatorname{Spec}$ of the structure map $k \to K$ to the corresponding fibre product for $f_Y$, i.e. a morphism $X_K \to Y_K$, which is compatible with the projections to $\operatorname{Spec} K$: $f$ followed by the second projection of the $Y$-pullback equals the second projection of the $X$-pullback. Assume further that for every $k$-algebra automorphism $\sigma$ of $K$, given a proof that $\operatorname{Spec}\sigma$ followed by $\operatorname{Spec}$ of $k \to K$ equals $\operatorname{Spec}$ of $k \to K$, the twist $\mathrm{id}_X \times \operatorname{Spec}\sigma$ followed by $f$ equals $f$ followed by $\mathrm{id}_Y \times \operatorname{Spec}\sigma$. Then there exist a morphism $g : X \to Y$ and a proof that $g$ followed by $f_Y$ equals $f_X$, such that $f$ is the base change $g \times \mathrm{id}_{\operatorname{Spec} K}$ (the pullback map induced by $g$ and two identities), and such that any $g'$ over $k$ whose base change is likewise $f$ satisfies $g' = g$.
--
--   This is Galois descent for morphisms (rather than for objects) along $\operatorname{Spec} K \to \operatorname{Spec} k$, for a possibly infinite Galois extension: a $K$-morphism between base changes that commutes with all Galois twists comes from a unique $k$-morphism. It is used in the construction of the descent of fibres of the relevant Néron-type objects over modular curves, in [`ModularCurve.JHNeronObjectAtP.exists_abqFibre_descent_zmodp`](thm.html#ModularCurve.JHNeronObjectAtP.exists_abqFibre_descent_zmodp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq
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
    ∃ g : X ⟶ Y, ∃ hg : g ≫ fY = fX,
      f = pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            g (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hg]) (by rw [Category.comp_id, Category.id_comp]) ∧
      ∀ (g' : X ⟶ Y) (hg' : g' ≫ fY = fX),
        f = pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))
              g' (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hg']) (by rw [Category.comp_id, Category.id_comp]) →
        g' = g := by sorry
