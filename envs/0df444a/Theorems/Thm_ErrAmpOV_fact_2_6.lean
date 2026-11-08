-- Prove2me | Theorems.Thm_ErrAmpOV_fact_2_6
-- name    : ErrAmpOV.fact_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:39:29.130063+00:00
-- url     : https://prove2.me/theorems/7fc84372-32ab-4ca1-b5be-d01876703e6b
-- title:
--   Fact 2.6 — brute-force circuits for OV and $k$-OV
-- statement:
--   The problem $\mathsf{OV}_{n,d}$ and, for each fixed $k$, the problem $k\text{-}\mathsf{OV}_{n,d}$ have deterministic circuits obtained by trying all pairs ($k$-tuples):
--
--   1. there is $C>0$ such that for all $n,d$, $\mathsf{OV}_{n,d}$ has circuits of size at most $C(n^2 d+1)$;
--   2. for every $k$ there is $C>0$ such that for all $n,d$, $k\text{-}\mathsf{OV}_{n,d}$ has circuits of size at most $C(n^k d+1)$.
--
--   The amplified circuit uses the first bound to decide the sub-instances left over after its last round.
--
--   Differences from the source:
--   - encoding: size O(n² · d) (O(n^k · d)) → size ≤ C·(n²·d + 1) (≤ C·(n^k·d + 1)); reason: at n = 0 or d = 0 the problem is a constant, which needs one gate although the printed bound is 0; for n, d ≥ 1 the two bounds agree up to the factor 2
--   - reading: O(n^k · d) with k fixed (Theorem 3.4: "Let k ∈ N") → C may depend on k, not on n, d; reason: k is a fixed constant on the page
--   - encoding: Boolean circuits, no gate basis fixed, size = number of gates → ErrAmpOV.Circuit: constant, NOT, AND, OR gates of fan-in at most 2, unbounded fan-out, inputs not counted, a list of output wires; a read of a gate not yet computed returns false; reason: the basis is unspecified on the page; complete fan-in-2 bases differ by a constant factor, and the out-of-range read only gives a free constant false
--   - encoding: inputs A, B: lists of n vectors in {0,1}^d, a_i · b_j = 0 over ℤ → x : Fin 2 × Fin n × Fin d → Bool, a_i[k] = x (0, i, k), b_j[k] = x (1, j, k), orthogonal iff no coordinate has both entries 1; reason: Lean convention; same 2nd input bits and the same predicate for 0/1 vectors
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), Fact 2.6, p.8

import Mathlib
import Definitions.Def_ErrAmpOV_SizeDecides
import Definitions.Def_ErrAmpOV_OV
import Definitions.Def_ErrAmpOV_kOV

set_option autoImplicit false

namespace ErrAmpOV

/-- Fact 2.6 (Deterministic brute-force circuits for OV and `k`-OV), p.8. (i) There is `C > 0`
such that for every `n, d`, `OV_{n,d}` has deterministic circuits of size at most
`C·(n²·d + 1)`. (ii) For every `k` there is `C > 0` such that for every `n, d`, `k-OV_{n,d}` has
deterministic circuits of size at most `C·(n^k·d + 1)`.

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
Fact 2.6, p.8.

**Formalization Note.** `O(n²·d)` is `≤ C·(n²·d + 1)` with `C` independent of `n, d` (and, in
(ii), depending on the fixed `k`). The `+ 1` only matters when `n = 0` or `d = 0`, where the
problem is a constant, which needs one gate; for `n, d ≥ 1` the two bounds are the same up to
the factor `2`. -/
theorem fact_2_6 :
    (∃ C : ℝ, 0 < C ∧ ∀ n d : ℕ, SizeDecides (C * ((n : ℝ) ^ 2 * d + 1)) (OV n d)) ∧
    (∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ n d : ℕ, SizeDecides (C * ((n : ℝ) ^ k * d + 1)) (kOV k n d)) := by sorry

end ErrAmpOV
