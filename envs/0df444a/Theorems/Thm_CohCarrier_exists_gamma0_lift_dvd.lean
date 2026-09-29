-- Prove2me | Theorems.Thm_CohCarrier_exists_gamma0_lift_dvd
-- name    : CohCarrier.exists_gamma0_lift_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/8262b12e-9c13-5e5c-bc2c-1c25e2eb511e
-- title:
--   Lifting units mod M to Γ₀(M) with ℓ M ∣ c
-- statement:
--   Let $M$ and $\ell$ be non-zero natural numbers and let $d$ be a unit of $\mathbb{Z}/M\mathbb{Z}$. Here $\Gamma_0(M)$ is the congruence subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of matrices whose lower-left entry is congruent to $0$ modulo $M$, and `gamma0Units M` is the homomorphism $\Gamma_0(M) \to (\mathbb{Z}/M\mathbb{Z})^\times$ sending $\gamma$ to the unit whose value is the reduction modulo $M$ of the lower-right entry $\gamma_{1,1}$ and whose inverse is the reduction of the upper-left entry $\gamma_{0,0}$ (the two reductions being mutually inverse because $\det \gamma = 1$ and $M \mid \gamma_{1,0}$). The assertion is that there exists an element $\sigma$ of $\Gamma_0(M)$ satisfying two conditions simultaneously: its image under `gamma0Units M` equals the given $d$, and the integer $\ell M$ divides the lower-left entry $\sigma_{1,0}$ of the underlying matrix in $\mathrm{SL}_2(\mathbb{Z})$. In other words, every unit modulo $M$ is realised as the lower-right residue of a matrix lying in the smaller group $\Gamma_0(\ell M) \subseteq \Gamma_0(M)$.
--
--   This is the standard compatibility statement allowing a diamond operator $\langle d \rangle$ at level $M$ to be computed using a lift that already lies in $\Gamma_0(\ell M)$, so that it commutes with the Hecke operator at $\ell$. It is used repeatedly in the construction and analysis of the Hecke action on the cohomological carrier, for instance in the identification of residual diamond characters and in the statements about Hecke eigenclasses and Frobenius characteristic polynomials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_gamma0_lift_dvd.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CongruenceSubgroup
open scoped MatrixGroups

theorem CohCarrier.exists_gamma0_lift_dvd (M ℓ : ℕ) [NeZero M] [NeZero ℓ] (d : (ZMod M)ˣ) :
    ∃ σ : Gamma0 M, gamma0Units M σ = d ∧ ((ℓ * M : ℕ) : ℤ) ∣ ((σ : SL(2, ℤ)) 1 0) := by sorry
