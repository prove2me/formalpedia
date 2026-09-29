-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_mem_riemannRochSpace_forall_hasValue_mul_of_exists_not_mem
-- name    : AlgebraicCurve.exists_mem_riemannRochSpace_forall_hasValue_mul_of_exists_not_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/4e4f28fa-aa52-5dd3-ab67-fe9da56a8a1a
-- title:
--   Interpolation of twisted values in a Riemann–Roch space
-- statement:
--   Let $k$ be an algebraically closed field and $F$ a field with a $k$-algebra structure satisfying `IsCurveOver k F`: every nonzero element of $F$ has a degree-zero principal divisor whose value at each place $v$ is $\operatorname{ord}_v$ of that element, each place has residue field finite over $k$, and $\Omega_{F/k}$ is free of rank one over $F$. Let $\iota$ be a finite index type, $E : \mathrm{Place}(k,F) \to_{\mathrm{f}} \mathbb{Z}$ a divisor, $v : \iota \to \mathrm{Place}(k,F)$ an injective family of places, and $t : \iota \to F$ with each $t_i \neq 0$ and $\operatorname{ord}_{v_i}(t_i) = E(v_i)$. Assume for each $i$ that the inclusion $L\bigl(E - \sum_{j} v_j\bigr) \subseteq L\bigl(E - \sum_{j \neq i} v_j\bigr)$ is strict, where $L(D) = \{f \in F : \text{the } \mathbb{Z}^{m0}\text{-valued adic valuation of } f \text{ at every place } w \text{ is at most } \exp(D(w))\}$, a $k$-subspace of $F$. Then for every $c : \iota \to k$ there exists $p \in L(E)$ such that for each $i$ the product $t_i p$ lies in the valuation subring of $v_i$ and its residue equals the image of $c_i$ in the residue field of $v_i$.
--
--   This is the standard interpolation consequence of the Riemann–Roch inequality $\ell(D) - \ell(D-P) \le 1$: in the non-special range one may prescribe, independently at finitely many places, the values of the functions in $L(E)$ after normalising by local parameters $t_i$. It is used in the construction of models of modular curves over places, where prescribed residues (compatible with Galois actions) must be realised by elements of a Riemann–Roch space attached to a divisor satisfying a largeness condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_mem_riemannRochSpace_forall_hasValue_mul_of_exists_not_mem.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_mem_riemannRochSpace_forall_hasValue_mul_of_exists_not_mem
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F] [IsCurveOver k F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Divisor k F) (v : ι → Place k F) (hv : Function.Injective v) (t : ι → F)
    (ht : ∀ i, t i ≠ 0 ∧ (v i).ord (t i) = E (v i))
    (hstep : ∀ i, ∃ g ∈ riemannRochSpace (E - ∑ j ∈ Finset.univ.erase i, Finsupp.single (v j) 1),
      g ∉ riemannRochSpace (E - ∑ j, Finsupp.single (v j) 1))
    (c : ι → k) :
    ∃ p ∈ riemannRochSpace E, ∀ i, (v i).HasValue (t i * p) (c i) := by sorry
