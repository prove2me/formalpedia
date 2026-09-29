-- Prove2me | Theorems.Thm_BlockCycleRotation_cf_spec
-- name    : BlockCycleRotation.cf_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:54:19.764374+00:00
-- url     : https://prove2.me/theorems/966f1c63-5a86-4caf-acb5-4c6b754510db
-- title:
--   The expansion produced by `cf` is normalised: nonempty, with positive entries and first entry at least `2`
-- statement:
--   The expansion produced by `cf` is normalised: nonempty, with positive entries and first entry at least `2`.
--
--   In Blomer–Bux this is **Heilbronn 1969**, “`cf` lands in normalised lists”. It is used in the proofs of `heilbronn_bijection`, `heilbronn_surjective`, `quadExpansion_spec`, `shift_expansion_bijection`, and 2 further result(s).
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Heilbronn 1969. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L337-L377

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.cf_spec : ∀ a' a : ℕ, 1 ≤ a' → a' < a → Nat.gcd a a' = 1 →
    cf a a' ≠ [] ∧ (∀ x ∈ cf a a', 1 ≤ x) ∧ (∀ x ∈ (cf a a').head?, 2 ≤ x) := by sorry
