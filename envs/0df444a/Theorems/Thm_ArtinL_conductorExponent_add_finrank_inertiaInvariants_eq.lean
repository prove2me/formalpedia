-- Prove2me | Theorems.Thm_ArtinL_conductorExponent_add_finrank_inertiaInvariants_eq
-- name    : ArtinL.conductorExponent_add_finrank_inertiaInvariants_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/7c3b1deb-8fa3-5c13-be4f-5fdf1db72e43
-- title:
--   Tame case: Artin conductor exponent plus inertia invariants equal n
-- statement:
--   Let $n$ be a natural number and let $\rho \colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) \to \mathrm{GL}_n(\mathbb C)$ be a group homomorphism (the Galois group being realised as the $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`), and assume [`GaloisFactorsThroughFiniteLevel ρ`](def/GaloisRep_Residual.html#L17): there is an intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$, finite-dimensional over $\mathbb Q$, such that every automorphism fixing $L$ pointwise is sent to $1$. Let $p$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$ with `A.LiesOverPrime p`, i.e. $p$ is a non-unit of $A$, and write $I_A$ for `A.inertiaSubgroupIn ℚ`, the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ inside its decomposition subgroup. Assume tameness in the form that the cardinality of the image subgroup $\rho(I_A)$ is coprime to $p$. The conclusion is the equality $$\mathrm{conductorExponent}(\rho,p) + \dim_{\mathbb C} V^{I_A} = n,$$ where $V^{I_A}$ is the subspace of $\mathbb C^n$ fixed by the matrix representation attached to $\rho$ restricted to $I_A$, and where $\mathrm{conductorExponent}(\rho,p)$ is, since $p$ is prime and a valuation subring over $p$ exists, the sum $\mathrm{codimInvariants}$ of $\rho$ along the inertia subgroup of some chosen valuation subring over $p$ plus the ceiling of the corresponding `swanConductor`. In particular the asserted equality holds with the conductor exponent computed at an arbitrary choice of place above $p$, not necessarily at $A$.
--
--   This is the computation of the Artin conductor exponent at a tamely ramified prime: the wild (Swan) part vanishes and the exponent reduces to the codimension of the inertia invariants, as in Serre's treatment of the Artin conductor. It is the local input used in the weight-one Deligne–Serre step [`DeligneSerre.eulerFactor_eq_and_tameLevel_of_weightOne_newform_qCoeff_eq_trace`](thm.html#DeligneSerre.eulerFactor_eq_and_tameLevel_of_weightOne_newform_qCoeff_eq_trace), where the level of the attached newform at $p$ is matched with the conductor exponent of the representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_conductorExponent_add_finrank_inertiaInvariants_eq.lean

import Mathlib
import Definitions.Def_ArtinL_Conductor
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem ArtinL.conductorExponent_add_finrank_inertiaInvariants_eq {n : ℕ}
    (ρ : Γℚ →* GL (Fin n) ℂ) (hρ : GaloisFactorsThroughFiniteLevel ρ)
    {p : ℕ} (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (htame : (Nat.card ((A.inertiaSubgroupIn ℚ).map ρ)).Coprime p) :
    ArtinL.conductorExponent ρ p + Module.finrank ℂ (ArtinL.inertiaInvariants ρ A) = n := by sorry
