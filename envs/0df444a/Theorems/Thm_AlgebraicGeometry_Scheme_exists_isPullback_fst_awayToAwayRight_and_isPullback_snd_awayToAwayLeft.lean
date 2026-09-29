-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_isPullback_fst_awayToAwayRight_and_isPullback_snd_awayToAwayLeft
-- name    : AlgebraicGeometry.Scheme.exists_isPullback_fst_awayToAwayRight_and_isPullback_snd_awayToAwayLeft
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/976f2ad4-f159-5e9c-8a74-bc0ced9e370c
-- title:
--   Overlap of two away-charts is the chart over S[1/rᵢrⱼ]
-- statement:
--   Let $S$ be a commutative ring, let $A$ be a scheme with a morphism $f\colon A \to \operatorname{Spec} S$, let $k$ be a natural number and let $r\colon \mathrm{Fin}\,k \to S$ be a family of elements of $S$. Suppose given, for each index $i$, a scheme $A'_i$ together with a morphism $f'_i\colon A'_i \to \operatorname{Spec} S[1/r_i]$ (the spectrum of the away-localisation $\mathrm{Localization.Away}\,(r_i)$) and a morphism $g_i\colon A'_i \to A$, such that for each $i$ the square with sides $g_i$, $f'_i$, $f$ and $\operatorname{Spec}$ of the localisation map $S \to S[1/r_i]$ is cartesian, i.e. $A'_i$ is the base change of $A$ along $\operatorname{Spec} S[1/r_i] \to \operatorname{Spec} S$. Then for any two indices $i, j$ there exists a morphism $f_{ij}$ from the chosen pullback $A'_i \times_A A'_j$ to $\operatorname{Spec} S[1/(r_ir_j)]$ such that both of the following squares are cartesian: the one with sides the first projection $A'_i \times_A A'_j \to A'_i$, $f_{ij}$, $f'_i$ and $\operatorname{Spec}$ of the ring map $S[1/r_i] \to S[1/(r_ir_j)]$ given by `IsLocalization.Away.awayToAwayRight`, and the one with sides the second projection, $f_{ij}$, $f'_j$ and $\operatorname{Spec}$ of $S[1/r_j] \to S[1/(r_ir_j)]$ given by `IsLocalization.Away.awayToAwayLeft`.
--
--   This is the standard statement that the overlap of two base-change charts $A'_i = A \times_S \operatorname{Spec} S[1/r_i]$ is itself a chart, namely the base change of $A$ to the basic open $D(r_ir_j)$, compatibly with both projections. It is used in the verification that local data on an affine cover by basic opens glue, in the treatment of invertible modules on schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_isPullback_fst_awayToAwayRight_and_isPullback_snd_awayToAwayLeft.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_isPullback_fst_awayToAwayRight_and_isPullback_snd_awayToAwayLeft
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    {k : ℕ} (r : Fin k → S)
    (A' : Fin k → Scheme.{u}) (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (Localization.Away (r i))))
    (g : ∀ i, A' i ⟶ A)
    (hg : ∀ i, IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))))
    (i j : Fin k) :
    ∃ fij : pullback (g i) (g j) ⟶ Spec (CommRingCat.of (Localization.Away (r i * r j))),
      IsPullback (pullback.fst (g i) (g j)) fij (f' i)
        (Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight (r i) (r j) :
          Localization.Away (r i) →+* Localization.Away (r i * r j)))) ∧
      IsPullback (pullback.snd (g i) (g j)) fij (f' j)
        (Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayLeft (r j) (r i) :
          Localization.Away (r j) →+* Localization.Away (r i * r j)))) := by sorry
