-- Prove2me | solution 1 for erdos_ginzburg_ziv
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T08:23:34.842989+00:00
-- url     : https://prove2.me/submissions/52e323a8-1167-440b-992a-e43700023d6f

import Mathlib.Combinatorics.Additive.ErdosGinzburgZiv

/-!
The **Erdős–Ginzburg–Ziv theorem** (conjectured 1935, proved 1961), in its classical form.

Among any `2n - 1` integers there are `n` whose sum is divisible by `n`.

This is a platform catalog port of Mathlib's `Int.erdos_ginzburg_ziv` (proved there via
Chevalley–Warning for the prime case and induction along the prime factorization for the
composite case), restated over `Fin (2 * n - 1)` so the statement is fully explicit.
-/

open Finset

/-- **Erdős–Ginzburg–Ziv**: among any `2n - 1` integers, some `n` have sum divisible by `n`. -/
theorem solution (n : ℕ) (a : Fin (2 * n - 1) → ℤ) :
    ∃ t : Finset (Fin (2 * n - 1)), t.card = n ∧ (n : ℤ) ∣ ∑ i ∈ t, a i := by
  obtain ⟨t, -, htc, hts⟩ :=
    Int.erdos_ginzburg_ziv (n := n) (s := (Finset.univ : Finset (Fin (2 * n - 1)))) a
      (by simp)
  exact ⟨t, htc, hts⟩
