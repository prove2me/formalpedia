-- Prove2me | Theorems.Thm_APFB05_relation_excluded_in_window
-- name    : APFB05.relation_excluded_in_window
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:01:30.758658+00:00
-- url     : https://prove2.me/theorems/782a98ec-d0c4-4b16-bd4e-b21abd98a24b
-- title:
--   A three-floor novelty chain is excluded below its cost window
-- statement:
--   Use the shared source vocabulary: a protocol serves a finite family through maintained sufficient records that it uses to realize each task. Family cost is the real infimum of calibrated whole-protocol bills. Admissibility additionally requires a serving protocol to exist and the infimum to fit capacity. The guarded B05 hypothesis prices tested, support-novel additions only when both the starting and enlarged families are admissible. All resource, calibration, support and realization arguments are shared between this hypothesis and the conclusion. Assume B05 and three tested insertions d₁, d₂ and r, each support-novel at its respective step. Assume S and the first two enlarged families are admissible. If capacity is below the cost of S plus three floors, the final enlargement by r is inadmissible. The final family's admissibility is the denied conclusion, not an extra hypothesis. Source: Paper 1 Supplement v9.28, lines 1787–1790, 1816–1826 and 2624–2625.
-- source:
--   Theorems/Thm_APFB05_relation_task.lean, declaration at line 115 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 1787–1790, 1816–1826 and 2624–2625.

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

theorem APFB05.relation_excluded_in_window
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
    (hn1 : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S d1)
    (hn2 : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (insert d1 S) d2)
    (hn3 : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (insert d2 (insert d1 S)) r)
    (hwindow : C g < familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) S + 3 * epsilon g) :
    ¬ familyAdmissible (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (C g) (insert r (insert d2 (insert d1 S))) := by sorry
