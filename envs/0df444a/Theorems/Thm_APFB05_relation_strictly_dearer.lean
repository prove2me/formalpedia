-- Prove2me | Theorems.Thm_APFB05_relation_strictly_dearer
-- name    : APFB05.relation_strictly_dearer
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:14:25.501246+00:00
-- url     : https://prove2.me/theorems/ef8e51b2-531e-4733-910d-5e22b2a542a8
-- title:
--   A tested novel relation makes its admitted family strictly dearer
-- statement:
--   Use the shared source vocabulary: a protocol serves a finite family through maintained sufficient records that it uses to realize each task. Family cost is the real infimum of calibrated whole-protocol bills. Admissibility additionally requires a serving protocol to exist and the infimum to fit capacity. The guarded B05 hypothesis prices tested, support-novel additions only when both the starting and enlarged families are admissible. All resource, calibration, support and realization arguments are shared between this hypothesis and the conclusion. Assume B05. Let r be tested and support-novel over S, and assume that S and its enlargement by r are both admissible. The enlarged family has strictly greater infimal cost than S. Strictness uses the positive floor. The theorem does not establish that any physical relation task meets the hypotheses or compare the family price with separately billed singleton tasks. Source: FOUNDATION_INPUTS B05 and B07a scope; Paper 1 Supplement v9.28, lines 1816–1826.
-- source:
--   Theorems/Thm_APFB05_no_free_rider.lean, declaration at line 36 (Sib v15; source-scoped review). FOUNDATION_INPUTS B05 and B07a scope; Paper 1 Supplement v9.28, lines 1816–1826.

import Theorems.Thm_APFPaper1_Source_not_supportNovel_of_carried
import Theorems.Thm_APFB05_relation_task_third_charge
import Theorems.Thm_APFB05_mark_mark_relation_three_floors
import Theorems.Thm_APFB05_relation_excluded_in_window

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

theorem APFB05.relation_strictly_dearer
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (S : Finset (D g)) (r : D g)
    (htested : tested g r)
    (hS : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) S)
    (hSr : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert r S))
    (hnew : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S r) :
    familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) S <
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (insert r S) := by sorry
