-- Prove2me | Theorems.Thm_AlgebraicGeometry_flat_and_surjective_of_forall_exists_iso_morphismRestrict_eq_pullback_fst
-- name    : AlgebraicGeometry.flat_and_surjective_of_forall_exists_iso_morphismRestrict_eq_pullback_fst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/f4c874cf-ec89-5ac5-aff0-8b77e68f9907
-- title:
--   Zariski-local triviality gives flatness and surjectivity
-- statement:
--   Let $S$, $D$, $B$, $G$ be schemes (in a fixed universe), let $g \colon G \to S$ be a morphism that is flat and surjective, and let $b \colon B \to S$ and $\pi \colon D \to B$ be morphisms. Assume the following local triviality hypothesis: for every point $p$ of $B$ there is an open subscheme $U$ of $B$ with $p \in U$, together with an isomorphism of schemes $e \colon \pi^{-1}(U) \xrightarrow{\ \sim\ } (U \hookrightarrow B \text{ followed by } b) \times_S G$, such that $e$ followed by the first projection $\mathrm{pr}_1$ of that fibre product equals the restriction $\pi \mid_U \colon \pi^{-1}(U) \to U$ of $\pi$ over $U$; here the fibre product is taken along the composite $U \hookrightarrow B \to S$ and along $g$. The conclusion is that $\pi$ is itself flat and surjective, i.e. both Mathlib morphism properties `Flat` and `Surjective` hold for $\pi$.
--
--   This is the standard statement that a morphism which is Zariski-locally on the target a base change of a fixed faithfully flat morphism is itself faithfully flat, flatness and surjectivity both being local on the target and stable under base change. It is used in the relative Picard part of the construction, where [`AlgebraicGeometry.RelPicard.flat_surjective_restrictPair_of_twoGluedSmoothCurves`](thm.html#AlgebraicGeometry.RelPicard.flat_surjective_restrictPair_of_twoGluedSmoothCurves) turns a local torsor structure (for a fixed group scheme $G$ over the base) into flatness and surjectivity of the restriction morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_flat_and_surjective_of_forall_exists_iso_morphismRestrict_eq_pullback_fst.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.flat_and_surjective_of_forall_exists_iso_morphismRestrict_eq_pullback_fst
    {S D B G : Scheme.{u}} (g : G ⟶ S) [Flat g] [Surjective g] (b : B ⟶ S) (π : D ⟶ B)
    (hloc : ∀ p : B, ∃ U : B.Opens, p ∈ U ∧
      ∃ e : (π ⁻¹ᵁ U : Scheme.{u}) ≅ pullback (U.ι ≫ b) g,
        e.hom ≫ pullback.fst (U.ι ≫ b) g = π ∣_ U) :
    Flat π ∧ Surjective π := by sorry
