-- Prove2me | Theorems.Thm_Algebra_isReduced_and_finrank_eq_natCard_algHom_of_forall_isMaximal_sq_eq
-- name    : Algebra.isReduced_and_finrank_eq_natCard_algHom_of_forall_isMaximal_sq_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/a0f3fdb3-1436-5e7d-8afc-3b47eac9d3d5
-- title:
--   Idempotent maximal ideals force a finite algebra to be Ωⁿ
-- statement:
--   Let $\Omega$ be an algebraically closed field and let $S$ be a commutative ring equipped with an $\Omega$-algebra structure which is finite as an $\Omega$-module, i.e. finite-dimensional as an $\Omega$-vector space. Assume that every maximal ideal $\mathfrak m$ of $S$ satisfies $\mathfrak m^2 = \mathfrak m$ (the square here being the ideal product). The conclusion is the conjunction of two assertions: first, $S$ is reduced, in the sense of Mathlib's `IsReduced`, so every nilpotent element of $S$ is zero; second, the $\Omega$-dimension of $S$, `Module.finrank Ω S`, equals the cardinality `Nat.card (S →ₐ[Ω] Ω)` of the set of $\Omega$-algebra homomorphisms $S \to \Omega$, this cardinality being taken in the sense of `Nat.card` (so a priori $0$ for an infinite set, although here the set is finite). No hypothesis of nontriviality is imposed on $S$; for $S$ trivial both sides of the dimension equality are $0$.
--
--   This is the statement that a finite $\Omega$-algebra all of whose maximal ideals are idempotent is isomorphic to a product of copies of $\Omega$, one for each point, in the form needed for the tangent-space computations of deformation theory: the dimension of the algebra counts its $\Omega$-points exactly. It is used by [`Algebra.isReduced_and_finrank_eq_natCard_algHom_of_forall_dualNumber_snd_eq_zero`](thm.html#Algebra.isReduced_and_finrank_eq_natCard_algHom_of_forall_dualNumber_snd_eq_zero), where the idempotence hypothesis is supplied by a vanishing condition on maps to the dual numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_isReduced_and_finrank_eq_natCard_algHom_of_forall_isMaximal_sq_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Algebra.isReduced_and_finrank_eq_natCard_algHom_of_forall_isMaximal_sq_eq
    (Ω : Type*) [Field Ω] [IsAlgClosed Ω] (S : Type*) [CommRing S] [Algebra Ω S] [Module.Finite Ω S]
    (h : ∀ 𝔪 : Ideal S, 𝔪.IsMaximal → 𝔪 ^ 2 = 𝔪) :
    IsReduced S ∧ Module.finrank Ω S = Nat.card (S →ₐ[Ω] Ω) := by sorry
