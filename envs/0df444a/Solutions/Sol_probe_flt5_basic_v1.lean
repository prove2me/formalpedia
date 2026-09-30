-- Prove2me | solution 1 for probe_flt5_basic_v1
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:42:32.68682+00:00
-- url     : https://prove2.me/submissions/d95c321b-56ab-4e00-973b-f4dc03c52a10

import Mathlib.NumberTheory.FLT.Basic
import Theorems.Thm_flt_five

/-- Fermat's Last Theorem for the exponent `5`, in Mathlib's `FermatLastTheoremFor` form.
`FermatLastTheoremFor 5` unfolds to `∀ a b c : ℕ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 5 + b ^ 5 ≠ c ^ 5`;
the platform theorem `flt_five` gives the same conclusion under the equivalent hypotheses
`0 < a`, `0 < b`, `0 < c`. -/
theorem solution : FermatLastTheoremFor 5 := by
  intro a b c ha hb hc
  exact flt_five a b c (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero hc)
