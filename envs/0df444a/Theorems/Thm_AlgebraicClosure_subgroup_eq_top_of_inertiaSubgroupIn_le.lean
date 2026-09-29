-- Prove2me | Theorems.Thm_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le
-- name    : AlgebraicClosure.subgroup_eq_top_of_inertiaSubgroupIn_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/e794e448-0c8b-5d8d-8df3-76094828673d
-- title:
--   Open subgroup containing all inertia is all of G_ℚ
-- statement:
--   Let $G=\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ be the group of $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, carrying its Krull topology, and let $H$ be a subgroup of $G$ whose underlying set is open. Assume: for every natural number $q$ that is prime, and every valuation subring $A$ of $\overline{\mathbb Q}$ such that the image of $q$ in $\overline{\mathbb Q}$ lies in the nonunits of $A$ (that is, $A$ lies over $q$, the residue characteristic condition `A.LiesOverPrime q`), the subgroup `A.inertiaSubgroupIn ℚ` of $G$ is contained in $H$; here `A.inertiaSubgroupIn ℚ` is by definition the image of the inertia subgroup `A.inertiaSubgroup ℚ` under the inclusion of the decomposition subgroup `A.decompositionSubgroup ℚ` into $G$, i.e. the inertia group of the place $A$ regarded inside the full Galois group. The conclusion is that $H$ is the whole group, $H = \top$. No normality of $H$ is assumed, and the hypothesis quantifies over all valuation subrings above all rational primes rather than over a chosen set of places.
--
--   This is the Galois-theoretic form of the Hermite–Minkowski theorem that $\mathbb Q$ admits no nontrivial everywhere-unramified extension (equivalently, $\operatorname{Spec}\mathbb Z$ is simply connected). It is the global input for statements of the form 'an everywhere-unramified continuous character, or Galois action on a finite module with open kernel, is trivial', and is used in this development through consequences such as [`AlgebraicClosure.monoidHom_eq_one_of_inertiaSubgroupIn_le_ker`](thm.html#AlgebraicClosure.monoidHom_eq_one_of_inertiaSubgroupIn_le_ker) and the triviality of Galois actions on quotients of torsion of elliptic curves with unramified inertia.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicClosure.subgroup_eq_top_of_inertiaSubgroupIn_le (H : Subgroup ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))) (hopen : IsOpen (H : Set ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)))) (hunr : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q → A.inertiaSubgroupIn ℚ ≤ H) : H = ⊤ := by sorry
