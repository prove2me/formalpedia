-- Prove2me | Theorems.Thm_CNFEncComplexity_ANRAM_anramEvaluates_cap
-- name    : CNFEncComplexity.ANRAM.anramEvaluates_cap
-- status  : Proved
-- author  : @bersubs
-- created : 2026-11-15T07:24:17.338193+00:00
-- url     : https://prove2.me/theorems/4b61b85c-5f05-4a01-87ac-66f4772edece
-- title:
--   Capping ANRAM advice queries by the time bound
-- statement:
--   With nonempty advice, capping the number of prefetched advice pairs at the time bound preserves the function evaluated by the ANRAM.
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614, Theorem 2, Section 3.2.

import Definitions.Def_CNFEncComplexity_AnramEvaluates

open CNFEncComplexity

theorem CNFEncComplexity.ANRAM.anramEvaluates_cap {n : ℕ} (prog : List Instr) (A : List Bool) (b t : ℕ)
    (f : (Fin n → Bool) → Bool) (hA : 0 < A.length) :
    AnramEvaluates prog A b t f ↔ AnramEvaluates prog A (min b t) t f := by sorry
