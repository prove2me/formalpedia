-- Prove2me | Theorems.Thm_APFB05_no_free_rider
-- name    : APFB05.no_free_rider
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:14:15.809201+00:00
-- url     : https://prove2.me/theorems/60ed9902-c186-4aa6-b08b-d33ec7f4d230
-- title:
--   A cheapest supplied candidate cannot contain an unnecessary novel task
-- statement:
--   Costs are the shared infimal family costs on fixed protocol and record data. The minimum-selection premise is written explicitly on an arbitrary set of finite families. Its identity with the full B07a original admissible configuration domain and total cost is not established. No uniqueness, replacement dynamics or physical optimization procedure is claimed. Assume B05, testedness and support novelty of r over S, and admissibility of both S and its enlargement. Let a supplied candidate set contain S, and suppose a supplied realized family belongs to that set and has cost no greater than every candidate. Then the realized family is not the enlargement of S by r. Source: FOUNDATION_INPUTS B05 and B07a scope; Paper 1 Supplement v9.28, lines 1816–1826.
-- source:
--   Theorems/Thm_APFB05_no_free_rider.lean, declaration at line 56 (Sib v15; source-scoped review). FOUNDATION_INPUTS B05 and B07a scope; Paper 1 Supplement v9.28, lines 1816–1826.

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

theorem APFB05.no_free_rider
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (S : Finset (D g)) (r : D g)
    (htested : tested g r)
    (hS : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) S)
    (hSr : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert r S))
    (hnew : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S r)
    (candidates : Set (Finset (D g))) (realized : Finset (D g))
    (hScand : S ∈ candidates)
    (hA2 : realized ∈ candidates ∧ ∀ T ∈ candidates,
      familyCost (wholeResource g) (calibration g) (maintained g)
          (sufficient g) (usesToRealize g) realized ≤
        familyCost (wholeResource g) (calibration g) (maintained g)
          (sufficient g) (usesToRealize g) T) :
    realized ≠ insert r S := by sorry
