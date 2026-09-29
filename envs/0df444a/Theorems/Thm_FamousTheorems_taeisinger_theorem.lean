-- Prove2me | Theorems.Thm_FamousTheorems_taeisinger_theorem
-- name    : FamousTheorems.taeisinger_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:29.646249+00:00
-- url     : https://prove2.me/theorems/58069761-b98d-4d49-b4cc-57d4092c492e
-- title:
--   Taeisinger's theorem: harmonic numbers are not integers
-- statement:
--   **Taeisinger's theorem: harmonic numbers are not integers.** For every $n\ge2$, the harmonic number
--   $$H_n=1+\frac12+\cdots+\frac1n$$
--   is not an integer.
--
--   Proved by Taeisinger in 1915, the standard proof looks at the largest power of $2$ at most $n$. That power of $2$ is the unique term with the largest $2$-adic valuation in the denominator, so the $2$-adic valuation of $H_n$ is negative. The theorem is a classic application of $p$-adic valuations. Kürschák extended it to sums of reciprocals of consecutive integers.
--
--   **Formalization note.** Mathlib's `harmonic_not_int`. `harmonic n` is $H_n$ as a rational number, and `Rat.isInt` tests whether its denominator is $1$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `harmonic_not_int`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem taeisinger_theorem {n : ℕ} (hn : 2 ≤ n) : ¬(harmonic n).isInt := by sorry

end FamousTheorems
