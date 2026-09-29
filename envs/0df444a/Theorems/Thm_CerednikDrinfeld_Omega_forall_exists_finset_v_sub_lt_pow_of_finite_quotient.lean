-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_forall_exists_finset_v_sub_lt_pow_of_finite_quotient
-- name    : CerednikDrinfeld.Omega.forall_exists_finset_v_sub_lt_pow_of_finite_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/ceba7e9d-729a-56ba-b6f3-3a5a4ddc3932
-- title:
--   Balls of K₀ are covered by finitely many small balls
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$ (the algebra map $R \to K_0$ being a localisation at the nonzero elements), let $\varpi \in R$ be irreducible, and assume the quotient $R/(\varpi)$ is finite. Let $K$ be a field extension of $K_0$ carrying a valuation $v =$ `Valued.v` with values in a linearly ordered commutative group with zero $\Gamma_0$, and suppose: every element of $R$ has $v(a) \le 1$ after mapping into $K$ (`hint`); conversely every $a \in K_0$ with $v(a) \le 1$ in $K$ is the image of an element of $R$ (`hv`); and the powers of $v(\varpi)$ are coinitial among the nonzero elements of $\Gamma_0$, i.e. for every $\varepsilon \neq 0$ there is $N$ with $v(\varpi)^N \le \varepsilon$ (`hq`). Let $\varpi_1$ be a pseudo-uniformiser of the pair $(K_0,K)$, that is an element $\varpi_1.\varpi \in K_0$ with $0 < v(\varpi_1.\varpi) < 1$ in $K$ and such that for every nonzero $a \in K_0$ there is $N$ with $v(\varpi_1.\varpi)^N \le v(a) \le v(\varpi_1.\varpi)^{-N}$. Then for every $n \in \mathbb{N}$ there is a finite subset $T \subseteq K_0$ such that every $a \in K_0$ with $v(a) \le v(\varpi_1.\varpi)^{-n}$ satisfies $v(a - t) < v(\varpi_1.\varpi)^{n}$ for some $t \in T$.
--
--   This is the local compactness of a discretely valued field with finite residue ring, read inside the larger valued field $K$ and phrased in elementary finite-covering form: every ball of $K_0$ of radius $v(\varpi_1)^{-n}$ is covered by finitely many balls of radius $v(\varpi_1)^{n}$. It serves to discharge the finiteness hypothesis of the statements about theta functions, the holomorphic ring and the Mumford quotient over an abstract pair $(K_0,K)$, in the concrete Bruhat–Tits situation $K_0 = \operatorname{Frac} R$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_forall_exists_finset_v_sub_lt_pow_of_finite_quotient.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.forall_exists_finset_v_sub_lt_pow_of_finite_quotient
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (ϖ₁ : PseudoUniformizer K₀ K) :
    ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ₁.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ₁.ϖ)) ^ n := by sorry
