-- Prove2me | Theorems.Thm_AutomorphicForm_finite_preimage_satakePow_pow
-- name    : AutomorphicForm.finite_preimage_satakePow_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/d13b28db-9444-5aeb-a2f5-986d2ac71175
-- title:
--   Finiteness of fibres of (a,b)↦(p_f(a,b),b^f)
-- statement:
--   Let $R$ be a commutative ring which is an integral domain, let $f$ be a natural number with $f \neq 0$, and let $c = (c_1,c_2)$ be a pair of elements of $R$. Here $\mathrm{satakePow}$ denotes the rank-two power-sum recursion on $R$: $\mathrm{satakePow}\,0\,s\,e = 2$, $\mathrm{satakePow}\,1\,s\,e = s$, and $\mathrm{satakePow}\,(n+2)\,s\,e = s\cdot \mathrm{satakePow}\,(n+1)\,s\,e - e\cdot\mathrm{satakePow}\,n\,s\,e$, so that on substituting $s = \alpha+\beta$, $e = \alpha\beta$ one recovers $\alpha^n+\beta^n$. The assertion is that the map $R \times R \to R \times R$ sending $p = (p_1,p_2)$ to $(\mathrm{satakePow}\,f\,p_1\,p_2,\ p_2^{\,f})$ has finite fibres: the preimage of the singleton $\{c\}$, that is the set of pairs $(a,b) \in R \times R$ with $\mathrm{satakePow}\,f\,a\,b = c_1$ and $b^{f} = c_2$, is a finite subset of $R \times R$. No bound on the cardinality of the fibre is asserted.
--
--   The polynomials $\mathrm{satakePow}$ are the rank-two power sums (Lucas sequences) expressing $\alpha^n+\beta^n$ in terms of $\alpha+\beta$ and $\alpha\beta$, so the map in question is the effect of $f$-th power base change on a pair (trace, determinant) of Satake parameters. The finiteness of its fibres is used in the construction of suitable auxiliary primes for the Hecke eigensystem argument, where it is cited by [`AutomorphicForm.exists_atoms_forall_exists_noAtomicMass_heckeWordSum_twistedCutTrace_sub_finrank_mul_const_mul_heckeWordSum_cutTrace_eq`](thm.html#AutomorphicForm.exists_atoms_forall_exists_noAtomicMass_heckeWordSum_twistedCutTrace_sub_finrank_mul_const_mul_heckeWordSum_cutTrace_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finite_preimage_satakePow_pow.lean

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.finite_preimage_satakePow_pow {R : Type*} [CommRing R] [IsDomain R]
    (f : ℕ) (hf : f ≠ 0) (c : R × R) :
    ((fun p : R × R => (satakePow f p.1 p.2, p.2 ^ f)) ⁻¹' {c}).Finite := by sorry
