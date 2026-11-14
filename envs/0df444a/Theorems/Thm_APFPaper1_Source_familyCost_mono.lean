-- Prove2me | Theorems.Thm_APFPaper1_Source_familyCost_mono
-- name    : APFPaper1.Source.familyCost_mono
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:03:48.436905+00:00
-- url     : https://prove2.me/theorems/c43c1b7d-3b08-4405-9c2e-0affe498e30a
-- title:
--   Feasible supersets have no smaller infimal family cost
-- statement:
--   The shared cost definition takes a real infimum of nonnegative calibrated protocol bills. Feasibility of T is retained to place this comparison on its intended domain; no cheapest protocol or attainment is assumed. This theorem alone does not supply a physical protocol representation or identify costs on infeasible families with the source's extended-real infinity convention. If S is contained in a finite family T and some protocol serves T, then the infimal family cost of S is at most that of T. A protocol serving T serves every member of S with the same sufficient maintained support and whole bill. B05 is not required. Source: Paper 1 Supplement v9.28, lines 1787–1790, 1816–1826 and 2624–2625.
-- source:
--   Theorems/Thm_APFPaper1_familyCost_mono.lean, declaration at line 30 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 1787–1790, 1816–1826 and 2624–2625.

import Definitions.Def_APFPaper1_FamilyCost
import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option autoImplicit false
namespace APFPaper1.Source
end APFPaper1.Source
open APFPaper1.Source

theorem APFPaper1.Source.familyCost_mono {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) {S T : Finset D} (hST : S ⊆ T)
    (hT : familyFeasible maintained sufficient usesToRealize T) :
    familyCost wholeResource calibration maintained sufficient usesToRealize S ≤
      familyCost wholeResource calibration maintained sufficient usesToRealize T := by sorry
