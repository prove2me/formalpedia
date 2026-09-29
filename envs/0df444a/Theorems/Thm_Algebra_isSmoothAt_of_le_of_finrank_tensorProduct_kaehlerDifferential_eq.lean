-- Prove2me | Theorems.Thm_Algebra_isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq
-- name    : Algebra.isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/c76e0a7f-6d41-5a6e-a46f-e56a767140b4
-- title:
--   Smoothness spreads to specialisations with constant differential rank
-- statement:
--   Let $R$ be a commutative ring in a universe $u$ that is a domain and a discrete valuation ring, and let $A$ be a commutative ring in the same universe, equipped with an $R$-algebra structure making it an $R$-algebra of finite type. Let $p$ and $q$ be prime ideals of $A$ with $q \le p$, so that the point $p$ of $\operatorname{Spec} A$ is a specialisation of $q$. Assume that $A$ is smooth over $R$ at $q$ in the sense of `Algebra.IsSmoothAt`, and that the two fibres of the module of Kähler differentials $\Omega^1_{A/R}$ have the same dimension, i.e. $$\dim_{k(p)}\bigl(k(p) \otimes_A \Omega^1_{A/R}\bigr) = \dim_{k(q)}\bigl(k(q) \otimes_A \Omega^1_{A/R}\bigr),$$ where $k(p)$ and $k(q)$ are the residue fields of $p$ and $q$ and the dimensions are `Module.finrank`. The conclusion is that $A$ is then smooth over $R$ at $p$, again in the sense of `Algebra.IsSmoothAt`.
--
--   This is the commutative-algebra content of the proof of Bosch–Lütkebohmert–Raynaud, *Néron Models*, 3.3, Lemma 1: over a discrete valuation ring, smoothness of a finite-type algebra propagates from a point to any specialisation of it at which the fibre dimension of the differentials does not jump. It is used in the Néron model infrastructure, in the characterisation of the vanishing of Néron's measure for the defect of smoothness in terms of the closed point landing in the smooth locus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct

universe u

theorem Algebra.isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (p q : Ideal A) [p.IsPrime] [q.IsPrime] (hqp : q ≤ p) [Algebra.IsSmoothAt R q]
    (h : Module.finrank p.ResidueField (p.ResidueField ⊗[A] Ω[A⁄R]) =
      Module.finrank q.ResidueField (q.ResidueField ⊗[A] Ω[A⁄R])) :
    Algebra.IsSmoothAt R p := by sorry
