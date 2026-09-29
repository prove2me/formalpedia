-- Prove2me | Theorems.Thm_CuspForm_linearIndependent_of_mem_intLattice
-- name    : CuspForm.linearIndependent_of_mem_intLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/cee428da-c7d5-546c-98e5-4f5775f2703f
-- title:
--   ℤ-independence implies ℂ-independence for integral cusp forms
-- statement:
--   Fix a natural number $N \neq 0$ and an integer weight $k$, and let $n$ be a natural number. Let $f : \mathrm{Fin}\, n \to \mathrm{CuspForm}(\Gamma_0(N), k)$ be a finite family of cusp forms of weight $k$ for the congruence subgroup $\Gamma_0(N)$. Assume first that every $f_i$ lies in [`CuspForm.intLattice N k`](def/CuspForm_IntegralStructure.html#L3), the $\mathbb Z$-submodule of $\mathrm{CuspForm}(\Gamma_0(N), k)$ spanned by those cusp forms all of whose $q$-expansion coefficients are rational integers, the $n$-th coefficient of a form $g$ being [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19) $g\, n$, namely the $n$-th coefficient of the $q$-expansion of $g$ taken with respect to the period $1$. Assume second that the family $f$ is linearly independent over $\mathbb Z$, i.e. as a family in the underlying $\mathbb Z$-module of $\mathrm{CuspForm}(\Gamma_0(N), k)$. The conclusion is that $f$ is linearly independent over $\mathbb C$.
--
--   This is the standard passage from an integral to a complex statement of independence for spaces of cusp forms with integral $q$-expansions: a $\mathbb Z$-basis of a lattice of cusp forms remains independent over $\mathbb C$. It is used in the construction of eigenvectors for characters of the Hecke algebra acting on such lattices, and hence in the integral-structure results on $\mathrm{CuspForm}(\Gamma_0(N), k)$ that follow.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_linearIndependent_of_mem_intLattice.lean

import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.linearIndependent_of_mem_intLattice {N : ℕ} [NeZero N] {k : ℤ} (n : ℕ) (f : Fin n → CuspForm (CongruenceSubgroup.Gamma0 N) k) (hf : ∀ i, f i ∈ CuspForm.intLattice N k) (h : LinearIndependent ℤ f) : LinearIndependent ℂ f := by sorry
