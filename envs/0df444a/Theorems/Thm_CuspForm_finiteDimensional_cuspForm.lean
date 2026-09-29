-- Prove2me | Theorems.Thm_CuspForm_finiteDimensional_cuspForm
-- name    : CuspForm.finiteDimensional_cuspForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/5de7cf04-d3f9-568f-b09d-ac9470508162
-- title:
--   Finite-dimensionality of S_k(Γ₀(N))
-- statement:
--   For every natural number $N$ that is non-zero and every integer $k$, the complex vector space of cusp forms of weight $k$ for the congruence subgroup $\Gamma_0(N)$ — that is, `CuspForm (CongruenceSubgroup.Gamma0 N) k` in Mathlib's sense: holomorphic functions on the upper half-plane satisfying the weight-$k$ transformation law under the image of $\Gamma_0(N)$ in $\mathrm{SL}_2(\mathbb{Z})$ acting on $\mathbb{H}$, and whose slash-translates are all bounded at infinity (the cuspidality condition) — is finite-dimensional over $\mathbb{C}$. No positivity, parity or other restriction is placed on $k$: negative and odd weights are allowed, in which case the assertion is still a genuine statement about a space that may well be zero. The level $N$ is arbitrary, subject only to $N \neq 0$.
--
--   This is the standard finiteness theorem for spaces of cusp forms, here at arbitrary level $N$ and arbitrary integer weight, Mathlib's own results of this kind being available at level one. It underlies the Hecke-theoretic arguments of the project: it is used to produce eigenforms and normalised eigenvectors for the Hecke operators, and in the weight-two vanishing statement for $\Gamma_0(N)$ attached to the genus formula.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_finiteDimensional_cuspForm.lean

import Mathlib.NumberTheory.ModularForms.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.finiteDimensional_cuspForm (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k) := by sorry
