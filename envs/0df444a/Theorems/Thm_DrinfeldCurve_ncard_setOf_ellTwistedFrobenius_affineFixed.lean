-- Prove2me | Theorems.Thm_DrinfeldCurve_ncard_setOf_ellTwistedFrobenius_affineFixed
-- name    : DrinfeldCurve.ncard_setOf_ellTwistedFrobenius_affineFixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/5d05beb6-73b6-5c8a-a636-0d6d3aa7115f
-- title:
--   Counting solutions of the elliptically twisted Drinfeld equations
-- statement:
--   Let $q$ be a prime and let $K$ be an algebraically closed field equipped with an $\mathbb{F}_{q^2}$-algebra structure, where $\mathbb{F}_{q^2}$ is realised as `GaloisField q 2`. Let $l_1, l_2, d \in \mathbb{F}_{q^2}$ satisfy $l_1 \neq l_2$, $l_1^{q+1} = 1$, $l_2^{q+1} = 1$, $d^q = -d$ and $d \neq 0$. Consider the set of pairs $u = (u_1,u_2) \in K \times K$ such that $u_1^{q^2} = l_1 u_1$, $u_2^{q^2} = l_2 u_2$ and $u_1^{q+1} - u_2^{q+1} = d$, the elements $l_1, l_2, d$ being mapped into $K$ along the structure map. The conclusion is a conjunction of two implications about the natural-number cardinality (`Set.ncard`) of this set: if $l_1 = -1$ or $l_2 = -1$ then it equals $q+1$; and if neither $l_1$ nor $l_2$ equals $-1$ then it equals $(q+1)^2$.
--
--   This is the finite-field computation underlying the count of fixed points of an elliptically twisted $q^2$-power Frobenius on the Drinfeld curve $xy^q - x^q y = 1$, the twisted equations having been diagonalised into eigen-coordinates $u_1, u_2$ with eigenvalues $l_1, l_2$ of norm one. It is used by [`DrinfeldCurve.natCard_place_restrictAlong_eq_smul_of_torus`](thm.html#DrinfeldCurve.natCard_place_restrictAlong_eq_smul_of_torus).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DrinfeldCurve_ncard_setOf_ellTwistedFrobenius_affineFixed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace DrinfeldCurve

theorem ncard_setOf_ellTwistedFrobenius_affineFixed
    (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] [Algebra (GaloisField q 2) K] [IsAlgClosed K]
    (l₁ l₂ d : GaloisField q 2) (h12 : l₁ ≠ l₂) (hl1 : l₁ ^ (q + 1) = 1) (hl2 : l₂ ^ (q + 1) = 1)
    (hd : d ^ q = -d) (hd0 : d ≠ 0) :
    ((l₁ = -1 ∨ l₂ = -1) →
      {u : K × K | u.1 ^ q ^ 2 = algebraMap (GaloisField q 2) K l₁ * u.1 ∧
          u.2 ^ q ^ 2 = algebraMap (GaloisField q 2) K l₂ * u.2 ∧
          u.1 ^ (q + 1) - u.2 ^ (q + 1) = algebraMap (GaloisField q 2) K d}.ncard = q + 1) ∧
    (¬ (l₁ = -1 ∨ l₂ = -1) →
      {u : K × K | u.1 ^ q ^ 2 = algebraMap (GaloisField q 2) K l₁ * u.1 ∧
          u.2 ^ q ^ 2 = algebraMap (GaloisField q 2) K l₂ * u.2 ∧
          u.1 ^ (q + 1) - u.2 ^ (q + 1) = algebraMap (GaloisField q 2) K d}.ncard = (q + 1) ^ 2) := by sorry
