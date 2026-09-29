-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_finset_forall_v_sub_lt_of_finite_residueField
-- name    : CerednikDrinfeld.Omega.exists_finset_forall_v_sub_lt_of_finite_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/899c366c-0c38-5420-8892-3b44ebcfb6df
-- title:
--   Balls in K₀ are covered by finitely many small discs
-- statement:
--   Let $K_0$ and $K$ be fields with $K$ a $K_0$-algebra, and let $K$ carry a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$; write $|x| = v(\text{image of } x \text{ in } K)$ for $x \in K_0$. Let $R_0$ be a discrete valuation domain which is a $K_0$-algebra with $K_0$ as its fraction field and whose residue field is finite, and assume $R_0$ is exactly the unit ball: an element $x \in K_0$ lies in the image of $R_0 \to K_0$ if and only if $|x| \le 1$. Let $\varpi$ be a pseudo-uniformiser of $K_0$ relative to $K$, that is, an element $\varpi.\varpi \in K_0$ with $0 < |\varpi.\varpi| < 1$ such that every nonzero $a \in K_0$ satisfies $|\varpi.\varpi|^N \le |a| \le |\varpi.\varpi|^{-N}$ for some $N \in \mathbb{N}$, and let $\varpi_0 \in R_0$ be irreducible with image $\varpi.\varpi$ in $K_0$. Then for every $n \in \mathbb{N}$ there is a finite subset $T$ of $K_0$ such that every $a \in K_0$ with $|a| \le |\varpi.\varpi|^{-n}$ satisfies $|a - t| < |\varpi.\varpi|^{n}$ for some $t \in T$.
--
--   This is the local-finiteness (local compactness) property of a discretely valued field with finite residue field, read through the valuation of the larger field $K$: each ball of radius $|\varpi|^{-n}$ in $K_0$ is covered by finitely many discs of radius $|\varpi|^{n}$. It is the finiteness input for the rigid-analytic arguments on Drinfeld's upper half plane in the Čerednik–Drinfeld part of the development, used for instance in the construction of places of invariant fields and in the computation of orders of vanishing of invariant functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_finset_forall_v_sub_lt_of_finite_residueField.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.Omega.exists_finset_forall_v_sub_lt_of_finite_residueField
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ K x) ≤ 1)
    (ϖ : Omega.PseudoUniformizer K₀ K) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ) :
    ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n := by sorry
