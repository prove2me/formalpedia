-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_hom_isPullback_opensInclusion_of_forall_affineOpens_isPullback
-- name    : AlgebraicGeometry.Scheme.exists_hom_isPullback_opensInclusion_of_forall_affineOpens_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/b1c68038-98f6-5266-abf4-c27b28117012
-- title:
--   Gluing a cartesian family over the affine opens
-- statement:
--   Let $M$ be a scheme. Suppose given, for each affine open $U$ of $M$ (an element of `M.affineOpens`), a scheme $Z_U$ together with a morphism $q_U : Z_U \to U$ to the open subscheme $U$, and, for each inclusion $U \le V$ of affine opens, a morphism $\rho_{U\le V} : Z_U \to Z_V$, subject to: $\rho_{U \le U} = \mathrm{id}_{Z_U}$; $\rho_{U\le V}$ followed by $\rho_{V\le W}$ equals $\rho_{U\le W}$; and, for each $U \le V$, the square with sides $\rho_{U\le V}$, $q_U$, $q_V$ and the inclusion $M.homOfLE$ of $U$ into $V$ is cartesian, so that $Z_U$ is the base change of $q_V$ along $U \hookrightarrow V$. The conclusion asserts the existence of a scheme $X$, a morphism $f : X \to M$ and morphisms $\iota_U : Z_U \to X$ such that: every $\iota_U$ is an open immersion; for every $U$ the square with sides $q_U$, $\iota_U$, the open immersion $U.1.\iota : U \to M$ and $f$ is cartesian, so $Z_U$ identifies with $f^{-1}(U)$ over $U$; $\rho_{U\le V}$ followed by $\iota_V$ equals $\iota_U$; every point of $X$ is the image under the underlying map of some $\iota_U$ of a point of $Z_U$; and for every property $P$ of morphisms of schemes that is Zariski-local at the target, if all $q_U$ satisfy $P$ then $f$ satisfies $P$.
--
--   This is the relative-representability gluing principle: a family of schemes over the affine opens of $M$, cartesian with respect to restriction, comes from a single morphism $f : X \to M$, with the transfer of any target-local property of morphisms from the pieces $q_U$ to $f$ included. It is used in the construction of the relative moduli scheme of quaternionic multiplication structures over a fine moduli scheme, where the local pieces representing the structures over each affine open are glued and four properties (finiteness, local finite presentation, separatedness, quasi-compactness) are read off from the last clause.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_hom_isPullback_opensInclusion_of_forall_affineOpens_isPullback.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_hom_isPullback_opensInclusion_of_forall_affineOpens_isPullback
    (M : Scheme.{u}) (Z : M.affineOpens → Scheme.{u}) (q : ∀ U : M.affineOpens, Z U ⟶ (U.1 : Scheme.{u}))
    (ρ : ∀ {U V : M.affineOpens}, U ≤ V → (Z U ⟶ Z V))
    (ρ_id : ∀ U : M.affineOpens, ρ (le_refl U) = 𝟙 (Z U))
    (ρ_comp : ∀ {U V W : M.affineOpens} (h₁ : U ≤ V) (h₂ : V ≤ W), ρ h₁ ≫ ρ h₂ = ρ (h₁.trans h₂))
    (hsq : ∀ {U V : M.affineOpens} (h : U ≤ V), IsPullback (ρ h) (q U) (q V) (M.homOfLE h)) :
    ∃ (X : Scheme.{u}) (f : X ⟶ M) (ι : ∀ U : M.affineOpens, Z U ⟶ X),
      (∀ U, IsOpenImmersion (ι U)) ∧
      (∀ U, IsPullback (q U) (ι U) U.1.ι f) ∧
      (∀ {U V : M.affineOpens} (h : U ≤ V), ρ h ≫ ι V = ι U) ∧
      (∀ x : X, ∃ (U : M.affineOpens) (y : Z U), (ι U).base y = x) ∧
      ∀ (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P], (∀ U, P (q U)) → P f := by sorry
