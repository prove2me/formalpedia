-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_finset_residueSystem_of_finite_quotient
-- name    : CerednikDrinfeld.Omega.exists_finset_residueSystem_of_finite_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/a38007a0-a48f-5e12-9adf-f3514fb6389f
-- title:
--   Finite residue system of a discrete valuation ring in an overfield
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$ (via an algebra map realising $K_0$ as the localisation of $R$ at its nonzero elements), let $\varpi \in R$ be an irreducible element, and assume the quotient ring $R/\varpi R$ is finite. Let $K$ be a field extension of $K_0$ equipped with a valuation $v$ taking values in a linearly ordered commutative group with zero $\Gamma_0$, and suppose that the valuation restricted to $K_0$ has valuation ring exactly $R$, in the sense that (i) $v(a) \le 1$ for every $a$ in the image of $R$ in $K$, and (ii) every $a \in K_0$ whose image in $K$ satisfies $v(a) \le 1$ lies in the image of $R \to K_0$. Then there is a finite subset $T \subseteq K_0$ such that: each $t \in T$ has $v(t) \le 1$ in $K$; every $a \in K_0$ with $v(a) \le 1$ satisfies $v(a - t) < 1$ for some $t \in T$; and distinct $t, t' \in T$ satisfy $1 \le v(t - t')$. Thus $T$ is a complete and pairwise separated set of representatives for the residue classes, with the valuation computed after transport to $K$.
--
--   This packages the standard fact that a discrete valuation ring with finite residue field admits a finite set of residue representatives, in the form needed when the valuation is read off from a larger valued field $K$ containing $K_0$. The three clauses are exactly the shape of the residue-system data used in the analysis of functions and tubes on the Drinfeld upper half plane, and the statement is used in the construction of edge regions as tubes around affine points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_finset_residueSystem_of_finite_quotient.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.Omega.exists_finset_residueSystem_of_finite_quotient
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    ∃ T : Finset K₀, (∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1) ∧
      (∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1) ∧
      (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 1 ≤ Valued.v (algebraMap K₀ K t - algebraMap K₀ K t')) := by sorry
