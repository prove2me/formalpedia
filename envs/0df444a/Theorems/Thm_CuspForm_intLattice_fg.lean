-- Prove2me | Theorems.Thm_CuspForm_intLattice_fg
-- name    : CuspForm.intLattice_fg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/28ef4908-40c0-582c-9f79-ccb374d48413
-- title:
--   Integral q-expansion lattice in S_k(Γ₀(N)) is finitely generated
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ and let $k$ be an integer. Consider the space $\mathrm{CuspForm}\ \Gamma_0(N)\ k$ of cusp forms of weight $k$ for the congruence subgroup $\Gamma_0(N)$, and inside it the $\mathbb{Z}$-submodule [`CuspForm.intLattice N k`](def/CuspForm_IntegralStructure.html#L3), defined as the $\mathbb{Z}$-span of the set of those cusp forms $f$ such that for every natural number $n$ there is an integer $m$ with $\mathrm{qCoeff}\ f\ n = m$, where $\mathrm{qCoeff}\ f\ n$ denotes the $n$-th coefficient of the $q$-expansion of $f$ taken with respect to the period $1$ (`qExpansion 1 f`). The theorem asserts that this submodule is finitely generated as a $\mathbb{Z}$-module, i.e. satisfies `Submodule.FG`. No hypothesis on $k$ beyond its being an integer is imposed, and the weight is not assumed positive or even; the spanning set is already closed under addition and integer scaling, so the lattice is exactly the set of cusp forms all of whose $q$-expansion coefficients are rational integers.
--
--   This is the standard integral structure on the space of cusp forms on $\Gamma_0(N)$: the $\mathbb{Z}$-module of forms with integral Fourier coefficients is of finite type, a finiteness statement strictly stronger than finite-dimensionality of $S_k(\Gamma_0(N))$ over $\mathbb{C}$. It is the finiteness input used downstream for the integrality of Hecke eigenvalues and for module-finiteness of the Hecke algebra acting on the lattice, and it is cited by the results on integral structures such as [`CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra`](thm.html#CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra) and [`CuspForm.IsNormalizedEigenform.exists_integralClosure_coe_eq_qCoeff`](thm.html#CuspForm.IsNormalizedEigenform.exists_integralClosure_coe_eq_qCoeff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_intLattice_fg.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_IntegralStructure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.intLattice_fg (N : ℕ) [NeZero N] (k : ℤ) : (CuspForm.intLattice N k).FG := by sorry
