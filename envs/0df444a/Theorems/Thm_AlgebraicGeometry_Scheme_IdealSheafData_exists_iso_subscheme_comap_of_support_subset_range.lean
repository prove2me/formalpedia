-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_iso_subscheme_comap_of_support_subset_range
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.exists_iso_subscheme_comap_of_support_subset_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/6846080e-0420-539a-b5e4-a887b07e8165
-- title:
--   Restriction of a closed subscheme along an open immersion containing its support
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe), let $I$ be an ideal sheaf datum on $X$, and let $\psi \colon Y \to X$ be a morphism which is an open immersion. Assume that the support of $I$, viewed as a subset of the underlying topological space of $X$ (the closed set cut out by $I$), is contained in the set-theoretic range of $\psi$. Then there exists an isomorphism of schemes $e$ from the closed subscheme of $Y$ associated with the pullback ideal sheaf `I.comap ψ` to the closed subscheme of $X$ associated with $I$, such that $e$ followed by the closed immersion `I.subschemeι` of $I$'s subscheme into $X$ equals the closed immersion `(I.comap ψ).subschemeι` of the subscheme of `I.comap ψ` into $Y$ followed by $\psi$. In other words, the square formed by $e$, the two canonical closed immersions and $\psi$ commutes, so the two closed subschemes are identified compatibly with their structure maps to $X$.
--
--   This is the statement that restricting a closed subscheme along an open immersion whose range contains the support changes nothing: the closed subscheme defined by the pulled-back ideal sheaf is canonically isomorphic, over $X$, to the original one. It is used to transfer properties of the closed subscheme cut out by an ideal sheaf (finiteness, ranks of structure sheaves) between a scheme and an open subscheme, and is cited in the treatment of relative effective Cartier divisors and of the relative Picard functor, in [`AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_and_supportedIn_of_support_subset_of_isOpenImmersion`](thm.html#AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_and_supportedIn_of_support_subset_of_isOpenImmersion) and [`AlgebraicGeometry.RelPicard.isFinite_and_finrank_subscheme_comap_sectionIdeal_pow_and_comap_I`](thm.html#AlgebraicGeometry.RelPicard.isFinite_and_finrank_subscheme_comap_sectionIdeal_pow_and_comap_I).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_iso_subscheme_comap_of_support_subset_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.exists_iso_subscheme_comap_of_support_subset_range
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (ψ : Y ⟶ X) [IsOpenImmersion ψ]
    (h : (I.support : Set X) ⊆ Set.range ψ) :
    ∃ e : (I.comap ψ).subscheme ≅ I.subscheme, e.hom ≫ I.subschemeι = (I.comap ψ).subschemeι ≫ ψ := by sorry
