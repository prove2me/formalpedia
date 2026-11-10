-- Prove2me | Theorems.Thm_EvasivePatterns_skolem_mahler_lech
-- name    : EvasivePatterns.skolem_mahler_lech
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:26:19.260198+00:00
-- url     : https://prove2.me/theorems/c83e88e3-adc2-4658-bfda-7233ca61d8b4
-- title:
--   Skolem–Mahler–Lech theorem [Lec53], as stated in §6
-- statement:
--   Let $K$ be a field of characteristic zero and $(u_n)_{n\ge0}$ a sequence in $K$ satisfying a linear recurrence with constant coefficients,
--   $$
--   u_{n+d} = c_0 u_n + c_1 u_{n+1} + \cdots + c_{d-1} u_{n+d-1} \qquad (n \ge 0).
--   $$
--   If $u_n = 0$ for infinitely many $n$, then some infinite arithmetic progression consists entirely of zeros: there are $a \ge 0$ and $d > 0$ with $u_{a + dt} = 0$ for all $t \ge 0$.
--
--   This is the classical theorem of Skolem, Mahler and Lech (C. Lech, *A note on recurring series*, Ark. Mat. 2 (1953)), cited by the paper and used in the proof of Lemma 6.1.
--
--   Differences from the source:
--   - encoding: a recurrence over characteristic zero → Mathlib LinearRecurrence over an arbitrary field of characteristic zero; reason: a constant-coefficient linear recurrence of any order
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), §6, p.9 (PDF p.10), lines 276–278 (citing [Lec53])

import Mathlib

namespace EvasivePatterns

/-- **The Skolem–Mahler–Lech theorem [Lec53], as stated in the paper.** If a recurrence over
characteristic zero has infinitely many zeros, then some infinite arithmetic progression consists
entirely of zeros.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), §6, printed p. 9 (PDF p. 10), lines 276–278, citing C. Lech, *A note on recurring
series*, Ark. Mat. 2 (1953), 417–421. A classical theorem cited (not proved) by the paper and used
in the proof of Lemma 6.1.

**Formalization Note** A recurrence is a constant-coefficient linear recurrence (Mathlib
`LinearRecurrence K`: `u (n + d) = Σ_{i<d} c_i u (n + i)` for all `n`) over an arbitrary field `K` of
characteristic zero. An infinite arithmetic progression is `{a + d t : t ∈ ℕ}` with `d > 0`. -/
theorem skolem_mahler_lech {K : Type*} [Field K] [CharZero K] (E : LinearRecurrence K)
    (u : ℕ → K) (hu : E.IsSolution u) (hinf : {n : ℕ | u n = 0}.Infinite) :
    ∃ a d : ℕ, 0 < d ∧ ∀ t : ℕ, u (a + d * t) = 0 := by sorry

end EvasivePatterns
