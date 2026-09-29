-- Prove2me | Theorems.Thm_CuspForm_finiteDimensional_Gamma1
-- name    : CuspForm.finiteDimensional_Gamma1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/2c300534-99a6-576e-8f3a-6353d94a2510
-- title:
--   Finite-dimensionality of S_k(Γ₁(M))
-- statement:
--   Let $M$ be a nonzero natural number and let $k$ be an arbitrary integer. Write $\Gamma_1(M)$ for `CongruenceSubgroup.Gamma1 M`, the congruence subgroup of matrices congruent to an upper triangular unipotent matrix modulo $M$, regarded (via the scoped matrix-group coercion) as a subgroup of $\mathrm{GL}_2(\mathbb{R})$. The assertion is that the space `CuspForm (CongruenceSubgroup.Gamma1 M) k` of weight-$k$ cusp forms for $\Gamma_1(M)$ — holomorphic functions on the upper half-plane satisfying the weight-$k$ transformation law under $\Gamma_1(M)$ and tending to zero at the cusps — is a finite-dimensional vector space over $\mathbb{C}$. No positivity or parity assumption is placed on the weight: the statement covers all integers $k$, including the negative and odd weights for which the space is in fact trivial, and no bound on the dimension is given, only its finiteness.
--
--   This is the classical finite-dimensionality theorem for spaces of cusp forms, here in level $\Gamma_1(M)$ and arbitrary integer weight. It is used in the identification of cusp forms of weight $2$ with regular differentials on the modular curve $X_1$, and in the finiteness argument underlying [`ModularCurve.exists_separable_aeval_smul_eq_zero_jOne_of_mem_adjoin_good`](thm.html#ModularCurve.exists_separable_aeval_smul_eq_zero_jOne_of_mem_adjoin_good).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_finiteDimensional_Gamma1.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.finiteDimensional_Gamma1 (M : ℕ) [NeZero M] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma1 M) k) := by sorry
