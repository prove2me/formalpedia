-- Prove2me | Theorems.Thm_Erdos287_primitive_affine_neighbor_capacity
-- name    : Erdos287.primitive_affine_neighbor_capacity
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T12:23:33.955155+00:00
-- url     : https://prove2.me/theorems/6faebb34-5779-5827-a301-51a2920524a2
-- title:
--   Cofactor capacity for consecutive multiples of primitive affine forms
-- statement:
--   Fix an affine form $P(t)=at+b$ and a cofactor interval $[L,U]$. Suppose every form $Q(t)=a't+b'$ in a finite set is primitive, and admits an identity $dQ(t)=cP(t)\pm1$ for a positive integer $d$ and a cofactor $c\in[L,U]$. The finite set has size at most $2\max(U+1-L,0)$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.primitive_affine_neighbor_capacity (S : Finset (ℕ × ℕ)) (a b L U : ℕ)
    (hprimitive : ∀ q ∈ S, q.1.Coprime q.2)
    (hneighbor : ∀ q ∈ S, ∃ (c d : ℕ) (side : Bool), c ∈ Finset.Icc L U ∧ 0 < d ∧
      c * a = d * q.1 ∧ (d : ℤ) * q.2 = (c : ℤ) * b + (if side then 1 else -1)) :
    S.card ≤ 2 * (U + 1 - L) := by sorry
