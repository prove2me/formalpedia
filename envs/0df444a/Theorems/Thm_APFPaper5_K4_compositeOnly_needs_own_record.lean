-- Prove2me | Theorems.Thm_APFPaper5_K4_compositeOnly_needs_own_record
-- name    : APFPaper5.K4.compositeOnly_needs_own_record
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:24:16.177131+00:00
-- url     : https://prove2.me/theorems/84173a84-1ed0-4104-8c21-d3ded5ccd69e
-- title:
--   Composite Only needs own record
-- statement:
--   Given the stated record dependence on equal-cross-weight summed books and sufficient record families for compositeOnly equality predicates, some such predicate requires a record outside the held union. The compared sum of two books is not an adopted mixture/additivity law. This is not physical local tomography, field selection, or a derivation of rates.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2221-2235'}, {'path': 'source/Theorems/Thm_APFPaper5_K4_composite_only_reading.lean', 'sha256': 'fcf4a9f1946d52406cc95920e36573d87c42f381d92af590cb28cada7050a0b5', 'line': 128, 'declaration': 'APFPaper5.K4.compositeOnly_needs_own_record'}]

import Definitions.Def_APFPaper5_K4_CompositeOnly
import Definitions.Def_APFPaper5_K4_TwoSheets
import Theorems.Thm_APFPaper5_K1_needs_own_record_of_separates
import Theorems.Thm_APFPaper5_K1_recordModel_supportNovel_of_needs_own_record
import Theorems.Thm_APFPaper5_K1_recordModel_economy_of_separation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K4
end APFPaper5.K4
open APFPaper5.K4
open APFPaper5.K3

theorem APFPaper5.K4.compositeOnly_needs_own_record {ι : Type*} {Rec : Type*} [DecidableEq Rec] {Val : Type*}
    (fam : ι → Finset Rec) (reads : Rec → Joint × Joint → Val)
    (verdict : ι → Joint × Joint → Prop) (S : Finset ι)
    (hS : ∀ r ∈ S.biUnion fam, ∀ x y : Joint × Joint,
      (∀ w : RecordWeights, w.u14 = w.u23 →
        linearRecord w x.1 + linearRecord w x.2 = linearRecord w y.1 + linearRecord w y.2) →
      reads r x = reads r y)
    (dComp : ℝ → ι)
    (hverdict : ∀ (t : ℝ) (x : Joint × Joint), verdict (dComp t) x ↔
      linearRecord compositeOnly x.1 + linearRecord compositeOnly x.2 = t)
    (hsound : ∀ (t : ℝ) (x y : Joint × Joint), (∀ r ∈ fam (dComp t), reads r x = reads r y) →
      (verdict (dComp t) x ↔ verdict (dComp t) y)) :
    ∃ t : ℝ, ¬ fam (dComp t) ⊆ S.biUnion fam := by sorry
