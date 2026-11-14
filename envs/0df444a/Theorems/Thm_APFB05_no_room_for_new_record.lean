-- Prove2me | Theorems.Thm_APFB05_no_room_for_new_record
-- name    : APFB05.no_room_for_new_record
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:58:05.754024+00:00
-- url     : https://prove2.me/theorems/e8b0d237-fb76-4b62-9b03-e8e4c9d14d3e
-- title:
--   Less than one floor of spare capacity excludes a new record
-- statement:
--   Use the shared source vocabulary: a protocol serves a finite family through maintained sufficient records that it uses to realize each task. Family cost is the real infimum of calibrated whole-protocol bills. Admissibility additionally requires a serving protocol to exist and the infimum to fit capacity. The guarded B05 hypothesis prices tested, support-novel additions only when both the starting and enlarged families are admissible. All resource, calibration, support and realization arguments are shared between this hypothesis and the conclusion. Assume B05, an admissible family S and a tested task d that is support-novel over S. If capacity minus the infimal cost of S is strictly smaller than the floor, then inserting d into S is not admissible. No particular cheapest protocol or attainment of the infimum is required. Novelty and testedness are hypotheses rather than conclusions. Source: Paper 1 Supplement v9.28, lines 1787–1790, 1816–1826 and 2624–2625.
-- source:
--   Theorems/Thm_APFB05_capacity_forced_family.lean, declaration at line 106 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 1787–1790, 1816–1826 and 2624–2625.

import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APF_B05_DeclaredInput_r2
import Theorems.Thm_APFB05_support_novel_chain_capacity_bound
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Classical
open APFPaper1.Source

namespace APFB05
end APFB05
open APFB05

theorem APFB05.no_room_for_new_record
    {Context : Type*} {D P R Record : Context → Type*} [∀ g, DecidableEq (D g)]
    (wholeResource : (g : Context) → P g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (maintained : (g : Context) → P g → Set (Record g))
    (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
    (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
    (tested : (g : Context) → D g → Prop)
    (C epsilon : Context → ℝ)
    (hB05 : MarginalFloor wholeResource calibration maintained sufficient usesToRealize tested C epsilon)
    (g : Context) (S : Finset (D g)) (d : D g)
    (htested : tested g d)
    (hS : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) S)
    (hnovel : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S d)
    (hspare : C g - familyCost (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S < epsilon g) :
    ¬ familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert d S) := by sorry
