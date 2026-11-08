-- Prove2me | Theorems.Thm_ErrAmpOV_fact_2_7
-- name    : ErrAmpOV.fact_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:38:31.391197+00:00
-- url     : https://prove2.me/theorems/08796ca0-9f0f-4da9-b9cc-25d1e65d634a
-- title:
--   Fact 2.7 — OV is downward self-reducible
-- statement:
--   Let $n=mt$ and partition the $n$ vectors of $A$ arbitrarily into $m$ blocks $A_1,\dots,A_m$ of $t$ vectors each, and likewise $B$ into $B_1,\dots,B_m$. Then
--   $$
--   \mathsf{OV}_{n,d}(A,B)=\bigvee_{i,j\in[m]}\mathsf{OV}_{t,d}(A_i,B_j).
--   $$
--
--   This identity reduces one instance to $m^2$ smaller instances, and it is the structure on which the whole amplification rests.
--
--   **Formalization Note** The partitions are bijections $e_1,e_2:[m]\times[t]\to[n]$; the $u$-th vector of $A_i$ is $a_{e_1(i,u)}$.
--
--   Differences from the source:
--   - generalization: 1 ≤ t ≤ n, t | n, m = n/t → any t, m and bijections e₁ e₂ : Fin m × Fin t ≃ Fin n; reason: the bijections force n = m t; the identity also holds at t = 0 or m = 0, where both sides are false, and the case of the page is the special case t ≥ 1
--   - encoding: inputs A, B: lists of n vectors in {0,1}^d, a_i · b_j = 0 over ℤ → x : Fin 2 × Fin n × Fin d → Bool, a_i[k] = x (0, i, k), b_j[k] = x (1, j, k), orthogonal iff no coordinate has both entries 1; reason: Lean convention; same 2nd input bits and the same predicate for 0/1 vectors
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), Fact 2.7, p.8

import Mathlib
import Definitions.Def_ErrAmpOV_OV

set_option autoImplicit false

namespace ErrAmpOV

/-- Fact 2.7 (OV is downward self-reducible), p.8. Partition the `n` vectors of `A` into `m`
blocks `A_0, …, A_{m-1}` of `t` vectors each, and likewise `B` into `B_0, …, B_{m-1}`; the
partitions are arbitrary bijections `e₁, e₂ : Fin m × Fin t ≃ Fin n` (vector `u` of block `i`
of `A` is `a_{e₁(i,u)}`). Then `OV_{n,d}(A, B) = ⋁_{i,j} OV_{t,d}(A_i, B_j)`.

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
Fact 2.7, p.8.

**Formalization Note.** The page assumes `1 ≤ t ≤ n`, `t ∣ n`, `m = n/t`. The bijections force
`n = m t`, and the identity holds for every `t`, `m` (including `t = 0`, where both sides are
false); so those hypotheses are dropped (a generalization). Indices are 0-based. -/
theorem fact_2_7 (n d t m : ℕ) (e₁ e₂ : Fin m × Fin t ≃ Fin n)
    (x : Fin 2 × Fin n × Fin d → Bool) :
    OV n d x = decide (∃ i j : Fin m, OV t d (fun q : Fin 2 × Fin t × Fin d =>
      if q.1 = 0 then x (0, e₁ (i, q.2.1), q.2.2) else x (1, e₂ (j, q.2.1), q.2.2)) = true) := by sorry

end ErrAmpOV
