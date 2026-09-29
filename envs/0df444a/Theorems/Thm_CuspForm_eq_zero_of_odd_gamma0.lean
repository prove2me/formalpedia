-- Prove2me | Theorems.Thm_CuspForm_eq_zero_of_odd_gamma0
-- name    : CuspForm.eq_zero_of_odd_gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/0372a34b-580e-586e-92c5-6e5ea5a59931
-- title:
--   Cusp forms of odd weight on Γ₀(N) vanish
-- statement:
--   Let $N$ be a natural number and $k$ an integer which is odd, i.e. $k = 2m+1$ for some integer $m$. Let $f$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_0(N)$ of $\mathrm{SL}_2(\mathbb{Z})$, in Mathlib's sense: a holomorphic function on the upper half-plane satisfying the weight-$k$ slash-invariance under every element of $\Gamma_0(N)$, viewed inside $\mathrm{GL}_2(\mathbb{R})$, and decaying at the cusps (the defining condition of `CuspForm`). The conclusion is that $f$ is the zero element of the space `CuspForm (CongruenceSubgroup.Gamma0 N) k`. Note that no positivity or lower bound on $k$, and no condition on $N$, is imposed; oddness of $k$ alone forces vanishing. The statement is the cusp-form analogue, for the particular subgroups $\Gamma_0(N)$, of the vanishing of odd-weight forms on any subgroup containing $-I$.
--
--   This is the standard observation that $-I \in \Gamma_0(N)$ for every level $N$, so that the weight-$k$ action of $-I$ multiplies a form by $(-1)^k$ and odd weight forces vanishing; it is the cusp-form spelling of a fact Mathlib records for modular forms. It is used to see that the Hecke algebra acting on odd-weight cusp forms of level $\Gamma_0(N)$ is trivial ([`CuspForm.heckeAlgebra.subsingleton_of_odd`](thm.html#CuspForm.heckeAlgebra.subsingleton_of_odd)), which keeps the weight conventions of the weight-lowering statements consistent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_eq_zero_of_odd_gamma0.lean

import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.eq_zero_of_odd_gamma0 (N : ℕ) (k : ℤ) (hk : Odd k)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : f = 0 := by sorry
