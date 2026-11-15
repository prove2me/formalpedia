-- Prove2me | Theorems.Thm_APFB05_whole_gt_parts_of_shared_lt_floor
-- name    : APFB05.whole_gt_parts_of_shared_lt_floor
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T19:12:29.942558+00:00
-- url     : https://prove2.me/theorems/4f27c236-acab-4636-ad78-547a1a3ee999
-- title:
--   Sharing below the floor makes the whole dearer
-- statement:
--   Under guarded B05, tested support novelty of r over S union T, and ledger admissibility before and after insertion, sharedCost(S,T)<epsilon implies k(S)+k(T)<k(insert r (S union T)).
-- source:
--   Theorems/Thm_APFB05_relation_residue.lean:74

import Definitions.Def_APF_B05_DeclaredInput_r2
import Definitions.Def_APFPaper5_K1_SharedCost

import Mathlib.Tactic.Linarith

set_option autoImplicit false
open APFPaper1.Source APFPaper5.K1


variable {Context : Type*} {D P R Record : Context → Type*} [∀ g, DecidableEq (D g)]
  (wholeResource : (g : Context) → P g → R g)
  (calibration : (g : Context) → R g → NNReal)
  (maintained : (g : Context) → P g → Set (Record g))
  (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
  (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
  (tested : (g : Context) → D g → Prop)
  (C epsilon : Context → ℝ)

theorem APFB05.whole_gt_parts_of_shared_lt_floor
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (S T : Finset (D g)) (r : D g) (htested : tested g r)
    (hU : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (S ∪ T))
    (hW : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert r (S ∪ T)))
    (hnew : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (S ∪ T) r)
    (hshare : sharedCost (familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g)) S T < epsilon g) :
    familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) S +
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) T <
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (insert r (S ∪ T)) := by sorry
