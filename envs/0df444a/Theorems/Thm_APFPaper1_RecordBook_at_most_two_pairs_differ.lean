-- Prove2me | Theorems.Thm_APFPaper1_RecordBook_at_most_two_pairs_differ
-- name    : APFPaper1.RecordBook.at_most_two_pairs_differ
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:53:05.290858+00:00
-- url     : https://prove2.me/theorems/61774230-d771-4727-a16d-0099b8c0b3ab
-- title:
--   At most two edges of a Boolean triangle disagree
-- statement:
--   This is the deterministic Boolean inequality appearing in the Supplement's three-context example. The theorem does not assume or construct a common physical assignment for separately tested contexts, introduce state weights, or prove the averaged probability inequality as part of this declaration. Those interpretations require their own data and, where appropriate, an averaging argument. For any three Boolean values a, b and c, the sum of the three disagreement indicators for ab, bc and ca is at most two. Each indicator is the natural number one when the pair differs and zero otherwise. There are no further hypotheses. Source: Paper 1 Supplement v9.28, lines 3666–3691.
-- source:
--   Theorems/Thm_APFPaper1_triangle_obstruction.lean, declaration at line 26 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 3666–3691.

import Mathlib.Data.Set.Defs

set_option autoImplicit false
namespace APFPaper1.RecordBook
end APFPaper1.RecordBook
open APFPaper1.RecordBook
universe uA

theorem APFPaper1.RecordBook.at_most_two_pairs_differ (a b c : Bool) :
    (if a ≠ b then 1 else 0) + (if b ≠ c then 1 else 0) + (if c ≠ a then 1 else 0) ≤ (2 : Nat) := by sorry
