-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isProper_isOpenImmersion_range_eq_preimage_comp_eq_of_isProper
-- name    : AlgebraicGeometry.exists_isProper_isOpenImmersion_range_eq_preimage_comp_eq_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/05cbb2a4-8ebf-5f05-a7c6-e016344fe47d
-- title:
--   Graph closure: proper modification extending a map to a proper scheme
-- statement:
--   Let $S$, $P$, $Y$ be schemes, $p \colon P \to S$ and $q \colon Y \to S$ morphisms with $q$ proper, and let $P$ be integral. Let $U$ be an open subscheme of $P$ whose inclusion $U.\iota \colon U \to P$ is quasi-compact, and assume the underlying set of $U$ is non-empty (hence dense, $P$ being irreducible). Let $g \colon U \to Y$ be a morphism which is a morphism over $S$ in the sense that $g$ followed by $q$ equals $U.\iota$ followed by $p$. The assertion is that there exist a scheme $P'$, morphisms $\beta \colon P' \to P$, $s \colon U \to P'$ and $g' \colon P' \to Y$ such that: $P'$ is integral; $\beta$ is proper; $s$ is an open immersion; $s$ followed by $\beta$ is the inclusion $U.\iota$; the set-theoretic range of the underlying continuous map of $s$ is exactly the preimage under the underlying map of $\beta$ of the open set $U \subseteq P$ (so that $\beta$ restricts to an isomorphism $\beta^{-1}(U) \to U$ identified by $s$); $s$ followed by $g'$ equals $g$; and $g'$ followed by $q$ equals $\beta$ followed by $p$, i.e. $g'$ is a morphism over $S$ extending $g$.
--
--   This is the standard construction of a proper modification of an integral scheme on which a morphism defined on a dense open subset, with proper target, extends: one takes the scheme-theoretic closure of the graph, the two projections furnishing $\beta$ and $g'$. It is used in the construction, for a valuation subring of the function field, of a proper modification with a point whose local ring has Krull dimension one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isProper_isOpenImmersion_range_eq_preimage_comp_eq_of_isProper.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isProper_isOpenImmersion_range_eq_preimage_comp_eq_of_isProper
    {P Y S : Scheme.{u}} (p : P ⟶ S) (q : Y ⟶ S) [IsProper q] [IsIntegral P]
    (U : P.Opens) [QuasiCompact U.ι] (hU : (U : Set P).Nonempty)
    (g : (U : Scheme.{u}) ⟶ Y) (hg : g ≫ q = U.ι ≫ p) :
    ∃ (P' : Scheme.{u}) (β : P' ⟶ P) (s : (U : Scheme.{u}) ⟶ P') (g' : P' ⟶ Y),
      IsIntegral P' ∧ IsProper β ∧ IsOpenImmersion s ∧ s ≫ β = U.ι ∧
      Set.range s.base = β.base ⁻¹' (U : Set P) ∧ s ≫ g' = g ∧ g' ≫ q = β ≫ p := by sorry
