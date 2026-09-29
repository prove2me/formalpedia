-- Prove2me | Theorems.Thm_CuspForm_mem_intLattice_iff
-- name    : CuspForm.mem_intLattice_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/4e13370e-0989-5d91-b526-ef66934b1fc4
-- title:
--   Membership in the integral lattice of cusp forms
-- statement:
--   Fix a level $N \in \mathbb{N}$ and a weight $k \in \mathbb{Z}$, and let $f$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_0(N)$. The integral lattice [`CuspForm.intLattice N k`](def/CuspForm_IntegralStructure.html#L3) is by definition the $\mathbb{Z}$-submodule of $\mathrm{CuspForm}(\Gamma_0(N), k)$ spanned by the set of those cusp forms all of whose $q$-expansion coefficients are rational integers, where the $n$-th coefficient of a function $g : \mathbb{H} \to \mathbb{C}$ is $\mathrm{qCoeff}\, g\, n$, the $n$-th coefficient of the $q$-expansion of $g$ taken with respect to the period $1$ (so $q = e^{2\pi i \tau}$). The theorem asserts that $f$ lies in this span if and only if for every $n \in \mathbb{N}$ there exists $m \in \mathbb{Z}$ with $\mathrm{qCoeff}\, f\, n = m$ in $\mathbb{C}$; that is, the spanning set is itself already a $\mathbb{Z}$-submodule, and membership in the lattice is equivalent to integrality of all coefficients of $f$ individually, with no sums of integral forms needed.
--
--   This is the working description of the integral structure on $S_k(\Gamma_0(N))$: the lattice of forms with integral $q$-expansion at $\infty$. It is used downstream in the treatment of the integral lattice, for instance in the statements about saturation of the coefficient maps, about injections of torsion quotients, and about integral bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_mem_intLattice_iff.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_IntegralStructure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.mem_intLattice_iff {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : f ∈ CuspForm.intLattice N k ↔ ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff f n = (m : ℂ) := by sorry
