-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_isPullback_of_forall_iff_of_openCover
-- name    : AlgebraicGeometry.exists_isClosedImmersion_isPullback_of_forall_iff_of_openCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/0295df5f-8ce8-5965-9d2c-f36304dcd3ad
-- title:
--   Gluing closed subschemes given on an open cover
-- statement:
--   Let $X$ be a scheme, $\iota$ a type, and for each $i : \iota$ let $g_i : U_i \to X$ be a quasi-compact open immersion of schemes, with the hypothesis that every point of $X$ lies in the set-theoretic image of some $g_i$. For each $i$ let $z_i : Z_i \to U_i$ be a closed immersion, and assume the agreement hypothesis: for all $i, j$, every scheme $T$ and all morphisms $P_i : T \to U_i$, $P_j : T \to U_j$ with $P_i$ followed by $g_i$ equal to $P_j$ followed by $g_j$, the morphism $P_i$ factors through $z_i$ if and only if $P_j$ factors through $z_j$. The conclusion asserts the existence of a scheme $K$ and a closed immersion $k : K \to X$ such that: (i) for each $i$ there is a morphism $Z_i \to K$ making the square with $z_i$, $g_i$ and $k$ a pullback, so $K \times_X U_i \cong Z_i$ over $U_i$; (ii) for every scheme $T$ and morphism $P : T \to X$, $P$ factors through $k$ if and only if for every $i$, every open subscheme $V$ of $T$ and every $P_V : V \to U_i$ with the inclusion $V \to T$ followed by $P$ equal to $P_V$ followed by $g_i$, the morphism $P_V$ factors through $z_i$; and (iii) $k$ is determined by this property up to agreement of subfunctors: if $k' : K' \to X$ is a closed immersion such that for each $i$ and every morphism $P : T \to U_i$ from any scheme $T$, the composite of $P$ with $g_i$ factors through $k'$ exactly when $P$ factors through $z_i$, then for every scheme $T$ and every $P : T \to X$, $P$ factors through $k'$ if and only if it factors through $k$.
--
--   This is the statement that closed subschemes prescribed on the members of an open cover of $X$ and agreeing on overlaps (as subfunctors of the functor of points) glue to a single closed subscheme, together with the expected local criterion for factorisation and the resulting uniqueness. It is used in the construction of auxiliary level structures on the fake elliptic curves occurring in the Čerednik–Drinfeld part of the development, via [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_of_openCover`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_of_openCover).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isClosedImmersion_isPullback_of_forall_iff_of_openCover.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_isClosedImmersion_isPullback_of_forall_iff_of_openCover
    {X : Scheme.{u}} {ι : Type u} (U : ι → Scheme.{u}) (g : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (g i)]
    [∀ i, QuasiCompact (g i)]
    (hcover : ∀ x : ↥X, ∃ i, x ∈ Set.range (g i).base)
    (Z : ι → Scheme.{u}) (z : ∀ i, Z i ⟶ U i) [∀ i, IsClosedImmersion (z i)]
    (hagree : ∀ (i j : ι) {T : Scheme.{u}} (Pᵢ : T ⟶ U i) (Pⱼ : T ⟶ U j),
      Pᵢ ≫ g i = Pⱼ ≫ g j → ((∃ Q : T ⟶ Z i, Q ≫ z i = Pᵢ) ↔ (∃ Q : T ⟶ Z j, Q ≫ z j = Pⱼ))) :
    ∃ (K : Scheme.{u}) (k : K ⟶ X), IsClosedImmersion k ∧
      (∀ i, ∃ zK : Z i ⟶ K, IsPullback (z i) zK (g i) k) ∧
      (∀ {T : Scheme.{u}} (P : T ⟶ X), (∃ Q : T ⟶ K, Q ≫ k = P) ↔
        ∀ (i : ι) (V : T.Opens) (PV : (V : Scheme.{u}) ⟶ U i), V.ι ≫ P = PV ≫ g i →
          ∃ Q : (V : Scheme.{u}) ⟶ Z i, Q ≫ z i = PV) ∧
      (∀ (K' : Scheme.{u}) (k' : K' ⟶ X), IsClosedImmersion k' →
        (∀ (i : ι) {T : Scheme.{u}} (P : T ⟶ U i),
          (∃ Q : T ⟶ K', Q ≫ k' = P ≫ g i) ↔ (∃ Q : T ⟶ Z i, Q ≫ z i = P)) →
        ∀ {T : Scheme.{u}} (P : T ⟶ X), (∃ Q : T ⟶ K', Q ≫ k' = P) ↔ (∃ Q : T ⟶ K, Q ≫ k = P)) := by sorry
