-- Prove2me | Theorems.Thm_APFB05_relation_task_third_charge
-- name    : APFB05.relation_task_third_charge
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:01:41.36199+00:00
-- url     : https://prove2.me/theorems/0719bcd1-a4e9-40e5-8d64-bac1cdf89388
-- title:
--   An admitted novel relation adds at least one floor
-- statement:
--   Use the shared source vocabulary: a protocol serves a finite family through maintained sufficient records that it uses to realize each task. Family cost is the real infimum of calibrated whole-protocol bills. Admissibility additionally requires a serving protocol to exist and the infimum to fit capacity. The guarded B05 hypothesis prices tested, support-novel additions only when both the starting and enlarged families are admissible. All resource, calibration, support and realization arguments are shared between this hypothesis and the conclusion. Assume B05, a tested task r, admissibility of S and its enlargement by r, and support novelty of r over S. The cost of the enlarged family is at least the cost of S plus the context's floor. This is a marginal family-cost inequality. It does not establish relation-task novelty or a premium beyond independently realized singleton costs. Source: Paper 1 Supplement v9.28, lines 1787–1790, 1816–1826 and 2624–2625.
-- source:
--   Theorems/Thm_APFB05_relation_task.lean, declaration at line 67 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 1787–1790, 1816–1826 and 2624–2625.

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

theorem APFB05.relation_task_third_charge
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
        (sufficient g) (usesToRealize g) S + epsilon g ≤
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (insert r S) := by sorry
