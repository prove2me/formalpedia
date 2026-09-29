-- Prove2me | Theorems.Thm_CuspForm_intLattice_free_and_finite
-- name    : CuspForm.intLattice_free_and_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/20a0633a-02f0-587d-b39e-ba9e7abde4ec
-- title:
--   Integral lattice of cusp forms is free of finite rank
-- statement:
--   Fix a level $N : \mathbb{N}$, assumed nonzero (via the `NeZero N` instance), and a weight $k : \mathbb{Z}$, and consider the complex vector space $\mathrm{CuspForm}\,(\Gamma_0(N))\,k$ of cusp forms of weight $k$ for the congruence subgroup `CongruenceSubgroup.Gamma0 N`. Inside it, [`CuspForm.intLattice N k`](def/CuspForm_IntegralStructure.html#L3) denotes the $\mathbb{Z}$-submodule spanned by the set of those cusp forms $f$ all of whose $q$-expansion coefficients are rational integers, i.e. such that for every $n : \mathbb{N}$ there is $m : \mathbb{Z}$ with $\mathrm{qCoeff}\,f\,n = (m : \mathbb{C})$, where $\mathrm{qCoeff}\,f\,n$ is the $n$-th coefficient of the $q$-expansion of $f$ of width $1$. The theorem asserts the conjunction of two statements about this submodule regarded as a $\mathbb{Z}$-module: it is free (`Module.Free ℤ`) and it is module-finite over $\mathbb{Z}$ (`Module.Finite ℤ`). Nothing is asserted about the rank of this lattice, in particular no comparison with $\dim_{\mathbb{C}} \mathrm{CuspForm}\,(\Gamma_0(N))\,k$, and no integrality or non-degeneracy hypothesis on the pair $(N,k)$ enters.
--
--   This is the structural statement that the integral $q$-expansion lattice in a space of cusp forms is a finitely generated free $\mathbb{Z}$-module, the basic input for discussing integral bases and for base change of the lattice. It is used in the treatment of Hecke operators on the integral lattice, in the injectivity of $q$-expansion maps after base change and localisation, and in the relative Picard/deformation-theoretic statements that presuppose freeness of the lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_intLattice_free_and_finite.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_IntegralStructure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.intLattice_free_and_finite (N : ℕ) [NeZero N] (k : ℤ) :
    Module.Free ℤ (CuspForm.intLattice N k) ∧ Module.Finite ℤ (CuspForm.intLattice N k) := by sorry
