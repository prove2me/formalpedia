-- Prove2me | Theorems.Thm_Algebra_isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable
-- name    : Algebra.isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/e3b646b2-ac0d-5dfb-a990-8d8ede6a8eef
-- title:
--   Ramification index one and separable residue extension give unramifiedness
-- statement:
--   Let $R$ and $S$ be commutative rings with an $R$-algebra structure on $S$, and assume $S$ is a Dedekind domain which is essentially of finite type over $R$ (Mathlib's `Algebra.EssFiniteType`). Let $p$ be a maximal ideal of $R$ and let $P$ be a prime ideal of $S$ lying over $p$, i.e. $p$ is the contraction of $P$ along $R \to S$; assume $P \neq 0$. Assume further that the ramification index of $P$ over $p$, in the sense of `Ideal.ramificationIdx'`, equals $1$, and that the residue field extension $(S/P)/(R/p)$ is separable. The conclusion is `Algebra.IsUnramifiedAt R P`: the localisation of $S$ at the prime $P$ is formally unramified over $R$, that is, unramified at $P$ in the sense of Grothendieck. Note that the statement is one implication only, from the Dedekind-theoretic data $e(P\mid p) = 1$ together with residual separability to formal unramifiedness, and not the converse or the full equivalence.
--
--   This is the classical comparison between unramifiedness in the ramification theory of Dedekind domains ($e = 1$ plus separable residue extension) and unramifiedness in the sense of Grothendieck (EGA IV 17.4.1), in the direction needed to exhibit unramified, hence after flatness étale, neighbourhoods. It is used in the construction of the relative group law on Jacobians of curves with good reduction, in the production of torsion points over suitable base changes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem Algebra.isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsDedekindDomain S] [Algebra.EssFiniteType R S]
    (p : Ideal R) [p.IsMaximal] (P : Ideal S) [P.IsPrime] [P.LiesOver p] (hP : P ≠ ⊥)
    (he : p.ramificationIdx' P = 1) [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Algebra.IsUnramifiedAt R P := by sorry
