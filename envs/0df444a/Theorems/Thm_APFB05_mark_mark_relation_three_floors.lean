-- Prove2me | Theorems.Thm_APFB05_mark_mark_relation_three_floors
-- name    : APFB05.mark_mark_relation_three_floors
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:57:42.728195+00:00
-- url     : https://prove2.me/theorems/a11b8e64-3532-4141-9fe1-f1385ac7ef22
-- title:
--   Three successive novel tasks add three floors
-- statement:
--   Use the shared source vocabulary: a protocol serves a finite family through maintained sufficient records that it uses to realize each task. Family cost is the real infimum of calibrated whole-protocol bills. Admissibility additionally requires a serving protocol to exist and the infimum to fit capacity. The guarded B05 hypothesis prices tested, support-novel additions only when both the starting and enlarged families are admissible. All resource, calibration, support and realization arguments are shared between this hypothesis and the conclusion. Assume B05 and three tested tasks d₁, d₂ and r. Starting from S, assume all four successive families are admissible and each task is support-novel over the family immediately preceding its insertion. Then the final family costs at least the original cost of S plus three times the floor. No physical identification of these tasks as two marks and their relation is derived. Source: Paper 1 Supplement v9.28, lines 1787–1790, 1816–1826 and 2624–2625.
-- source:
--   Theorems/Thm_APFB05_relation_task.lean, declaration at line 86 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 1787–1790, 1816–1826 and 2624–2625.

import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APF_B05_DeclaredInput_r2
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open APFPaper1.Source




variable {Context : Type*} {D P R Record : Context → Type*} [∀ g, DecidableEq (D g)]
  (wholeResource : (g : Context) → P g → R g)
  (calibration : (g : Context) → R g → NNReal)
  (maintained : (g : Context) → P g → Set (Record g))
  (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
  (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
  (tested : (g : Context) → D g → Prop)
  (C epsilon : Context → ℝ)

theorem APFB05.mark_mark_relation_three_floors
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (S : Finset (D g)) (d1 d2 r : D g)
    (ht1 : tested g d1) (ht2 : tested g d2) (htr : tested g r)
    (h0 : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) S)
    (h1 : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert d1 S))
    (h2 : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert d2 (insert d1 S)))
    (h3 : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert r (insert d2 (insert d1 S))))
    (hn1 : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S d1)
    (hn2 : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (insert d1 S) d2)
    (hn3 : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (insert d2 (insert d1 S)) r) :
    familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) S + 3 * epsilon g ≤
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (insert r (insert d2 (insert d1 S))) := by sorry
