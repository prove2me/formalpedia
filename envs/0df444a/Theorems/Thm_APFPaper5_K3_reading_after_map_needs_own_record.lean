-- Prove2me | Theorems.Thm_APFPaper5_K3_reading_after_map_needs_own_record
-- name    : APFPaper5.K3.reading_after_map_needs_own_record
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T08:14:14.735446+00:00
-- url     : https://prove2.me/theorems/4694041a-cb84-4dd5-b157-0ab07bbcc505
-- title:
--   Reading after map needs own record
-- statement:
--   Assume the held records depend only on plainAfterTurn, a map exposes a common turn, and the supplied distinction family exactly expresses post-map profile equality with sufficient record families. Some such distinction requires a record outside the held union. These theorems conclude record non-inclusion, not economic elimination or physical B05 support novelty. Required records, hsound, availability of a smaller configuration and original A2 binding are not supplied here.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1650,2221-2235'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_economy_instances.lean', 'sha256': '7e56a14b89897b37466d576ab71f614813db6c286f91ed745fc263f35b349fb9', 'line': 39, 'declaration': 'APFPaper5.K3.reading_after_map_needs_own_record'}]

import Definitions.Def_APFPaper5_K4_TwoSheets
import Theorems.Thm_APFPaper5_K1_needs_own_record_of_separates
import Theorems.Thm_APFPaper5_K1_recordModel_supportNovel_of_needs_own_record
import Theorems.Thm_APFPaper5_K1_recordModel_economy_of_separation
import Theorems.Thm_APFPaper5_K3_firstOrder_of_two_directions
import Theorems.Thm_APFPaper5_K3_two_directions_needed
import Theorems.Thm_APFPaper5_K3_seen_common_turn_splits_an_object
import Theorems.Thm_APFPaper5_K4_two_sheets_separate_more
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3
open APFPaper5.K1

universe u v
variable {ι : Type u} {Rec : Type v} [DecidableEq Rec]

theorem APFPaper5.K3.reading_after_map_needs_own_record {Val : Type*} (fam : ι → Finset Rec)
    (reads : Rec → Held2 → Val) (verdict : ι → Held2 → Prop) (S : Finset ι)
    (hS : ∀ r ∈ S.biUnion fam, ∀ x y : Held2, plainAfterTurn x = plainAfterTurn y →
      reads r x = reads r y)
    (T : Held2 → Held2) (hseen : ¬ CommonTurnUnseenAfter T)
    (dAfter : (ℝ × ℝ × (ℝ × ℝ × ℝ) → Prop) → ι)
    (hverdict : ∀ (Q : ℝ × ℝ × (ℝ × ℝ × ℝ) → Prop) (h : Held2),
      verdict (dAfter Q) h ↔ plainAfterTurn (T h) = Q)
    (hsound : ∀ (Q : ℝ × ℝ × (ℝ × ℝ × ℝ) → Prop) (x y : Held2),
      (∀ r ∈ fam (dAfter Q), reads r x = reads r y) →
        (verdict (dAfter Q) x ↔ verdict (dAfter Q) y)) :
    ∃ Q : ℝ × ℝ × (ℝ × ℝ × ℝ) → Prop, ¬ fam (dAfter Q) ⊆ S.biUnion fam := by sorry
