-- Prove2me | Theorems.Thm_APFPaper5_K3_rate_needs_own_record
-- name    : APFPaper5.K3.rate_needs_own_record
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T08:14:11.227312+00:00
-- url     : https://prove2.me/theorems/5859bca8-0b17-462c-93b0-0e4f68bc1383
-- title:
--   Rate needs own record
-- statement:
--   Assume held records depend only on the two component costs and plain recombination, and quarter-record equality distinctions have sufficient record families. Some quarter-record distinction needs a record outside the held union. These theorems conclude record non-inclusion, not economic elimination or physical B05 support novelty. Required records, hsound, availability of a smaller configuration and original A2 binding are not supplied here.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1650,2221-2235'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_economy_instances.lean', 'sha256': '7e56a14b89897b37466d576ab71f614813db6c286f91ed745fc263f35b349fb9', 'line': 70, 'declaration': 'APFPaper5.K3.rate_needs_own_record'}]

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

theorem APFPaper5.K3.rate_needs_own_record {Val : Type*} (fam : ι → Finset Rec)
    (reads : Rec → Held2 → Val) (verdict : ι → Held2 → Prop) (S : Finset ι)
    (hS : ∀ r ∈ S.biUnion fam, ∀ x y : Held2, recA x = recA y → recB x = recB y →
      recSum x = recSum y → reads r x = reads r y)
    (dQuarter : ℝ → ι) (hverdict : ∀ (t : ℝ) (h : Held2), verdict (dQuarter t) h ↔ recQuarter h = t)
    (hsound : ∀ (t : ℝ) (x y : Held2), (∀ r ∈ fam (dQuarter t), reads r x = reads r y) →
      (verdict (dQuarter t) x ↔ verdict (dQuarter t) y)) :
    ∃ t : ℝ, ¬ fam (dQuarter t) ⊆ S.biUnion fam := by sorry
