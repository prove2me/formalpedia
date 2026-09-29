-- Prove2me | Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic
-- name    : CuspForm.finiteDimensional_of_isArithmetic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/3eaacdc5-f6ba-524f-b5f6-1207ebd87fc8
-- title:
--   Finite-dimensionality of cusp forms for arithmetic G
-- statement:
--   Let $\mathcal{G}$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$ which is arithmetic (the Mathlib predicate `Subgroup.IsArithmetic`) and all of whose elements have determinant one (the predicate `Subgroup.HasDetOne`, which is what provides the $\mathbb{C}$-module structure on the space of forms), and let $k$ be an arbitrary integer, with no positivity or parity restriction. Then the space `CuspForm 𝒢 k` of weight-$k$ cusp forms on $\mathcal{G}$, that is, of holomorphic functions on the upper half-plane satisfying the weight-$k$ slash invariance under $\mathcal{G}$ together with the cuspidal decay condition at the cusps, is a finite-dimensional complex vector space. No dimension formula, and no nonvanishing or vanishing statement for particular $k$, is asserted: the conclusion is exactly the `FiniteDimensional ℂ (CuspForm 𝒢 k)` instance.
--
--   This is the classical finite-dimensionality theorem for spaces of cusp forms on an arithmetic group, in the form of a typeclass instance usable for arbitrary arithmetic $\mathcal{G}$ of determinant one. It is what makes the Hecke operators on cusp forms of level $\Gamma_0(N)$ a commuting family of endomorphisms of a finite-dimensional space, and is invoked throughout the treatment of eigenforms, of Eichler–Shimura cohomology and of the $q$-expansion arguments used in level changing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_finiteDimensional_of_isArithmetic.lean

import Mathlib.NumberTheory.ModularForms.QExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups

theorem CuspForm.finiteDimensional_of_isArithmetic (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] [𝒢.HasDetOne] (k : ℤ) : FiniteDimensional ℂ (CuspForm 𝒢 k) := by sorry
