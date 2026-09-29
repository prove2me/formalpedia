-- Prove2me | Theorems.Thm_CuspForm_finiteDimensional_Gamma0
-- name    : CuspForm.finiteDimensional_Gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/d4990a57-82fa-5677-bf03-0541b34d4fe3
-- title:
--   Finite-dimensionality of S_k(Γ₀(N))
-- statement:
--   Let $N$ be a natural number that is nonzero, and let $k$ be an arbitrary integer (no positivity or parity restriction is imposed; for $k$ in the ranges where the space vanishes the assertion is vacuous). Consider the congruence subgroup $\Gamma_0(N)$, consisting of the determinant-one integral $2\times 2$ matrices whose lower-left entry is divisible by $N$, regarded as a group of real $2\times 2$ matrices, and the complex vector space $\mathrm{CuspForm}\,(\Gamma_0(N))\,k = S_k(\Gamma_0(N))$ of weight-$k$ cusp forms for it: holomorphic functions on the upper half-plane which are invariant under the weight-$k$ slash action of $\Gamma_0(N)$ and which vanish at the cusps, in the sense that every translate under the relevant group elements tends to $0$ as the imaginary part tends to infinity. The assertion is that this space is finite-dimensional as a vector space over $\mathbb{C}$.
--
--   This is the classical finite-dimensionality of the space of cusp forms of weight $k$ and level $N$, specialised to the group $\Gamma_0(N)$ in which the modularity statements of the argument are phrased (notably $S_2(\Gamma_0(N))$ and its normalised Hecke eigenforms). It is invoked throughout the newform and Hecke-algebra part of the development, for instance in the construction of bases attached to the cohomological realisation of modular forms and in the characterisation of newforms by their Hecke eigenvalues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_finiteDimensional_Gamma0.lean

import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups

theorem CuspForm.finiteDimensional_Gamma0 (N : ℕ) [NeZero N] (k : ℤ) : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k) := by sorry
