-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isFinite_of_forall_isFinite_isPullback_of_isProper_of_isAdicComplete
-- name    : AlgebraicGeometry.exists_isFinite_of_forall_isFinite_isPullback_of_isProper_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/9009fb1b-0d1f-5dbe-a566-198cf90540dc
-- title:
--   Grothendieck existence for finite morphisms over a complete base
-- statement:
--   Let $R$ be a Noetherian commutative ring which is $I$-adically complete for an ideal $I \subseteq R$, let $X$ be a scheme and $f : X \to \operatorname{Spec} R$ a proper morphism. Suppose given, for each $n \in \mathbb{N}$, a morphism $sR_n : \operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec} R$ assumed to be $\operatorname{Spec}$ of the quotient map, and morphisms $tR_n : \operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec}(R/I^{n+2})$ with $tR_n$ followed by $sR_{n+1}$ equal to $sR_n$; write $X_n := X \times_{\operatorname{Spec} R} \operatorname{Spec}(R/I^{n+1})$ for the chosen pullback. Suppose given transition morphisms $xn_n : X_n \to X_{n+1}$ compatible with the two projections, namely $xn_n$ followed by the first projection of $X_{n+1}$ is the first projection of $X_n$, and $xn_n$ followed by the second projection is the second projection of $X_n$ followed by $tR_n$. Finally, suppose given schemes $Y_n$, finite morphisms $g_n : Y_n \to X_n$ and morphisms $yn_n : Y_n \to Y_{n+1}$ such that each square formed by $yn_n$, $g_n$, $g_{n+1}$, $xn_n$ is cartesian. The conclusion asserts the existence of a scheme $Y_f$, a finite morphism $G : Y_f \to X$, and isomorphisms $e_n : Y_f \times_X X_n \xrightarrow{\sim} Y_n$ (the fibre product taken along the first projection $X_n \to X$) such that $e_n$ followed by $g_n$ is the second projection $Y_f \times_X X_n \to X_n$, and such that the pullback map induced by $\mathrm{id}_{Y_f}$, $xn_n$ and $\mathrm{id}_X$, followed by $e_{n+1}$, equals $e_n$ followed by $yn_n$.
--
--   This is Grothendieck's existence theorem in formal geometry in the case of finite morphisms: a compatible system of finite schemes over the truncations $X_n$ of a proper $X$ over an $I$-adically complete Noetherian ring descends to a single finite scheme over $X$, with prescribed identifications of its truncations. It is used in the project to produce global finite morphisms from levelwise data, and is cited by the results on extending morphisms from compatible systems of truncations and on constructing finite morphisms from pointwise data over a complete base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isFinite_of_forall_isFinite_isPullback_of_isProper_of_isAdicComplete.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_isFinite_of_forall_isFinite_isPullback_of_isProper_of_isAdicComplete
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1 + 1))))
    (htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n)

    (xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1)))
    (hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n))
    (hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n)

    (Y : ℕ → Scheme.{u}) (g : ∀ n : ℕ, Y n ⟶ Limits.pullback f (sR n)) [∀ n : ℕ, IsFinite (g n)]
    (yn : ∀ n : ℕ, Y n ⟶ Y (n + 1))
    (hY : ∀ n : ℕ, IsPullback (yn n) (g n) (g (n + 1)) (xn n)) :
    ∃ (Yf : Scheme.{u}) (G : Yf ⟶ X) (_ : IsFinite G)
      (e : ∀ n : ℕ, Limits.pullback G (Limits.pullback.fst f (sR n)) ≅ Y n),

      (∀ n : ℕ, (e n).hom ≫ g n = Limits.pullback.snd G (Limits.pullback.fst f (sR n))) ∧

      (∀ n : ℕ,
        Limits.pullback.map G (Limits.pullback.fst f (sR n)) G (Limits.pullback.fst f (sR (n + 1))) (𝟙 Yf) (xn n) (𝟙 X)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hxn₁]) ≫ (e (n + 1)).hom =
          (e n).hom ≫ yn n) := by sorry
