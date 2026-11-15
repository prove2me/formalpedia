-- Prove2me | Theorems.Thm_APFB05_relation_residue_ge_floor_sub_shared
-- name    : APFB05.relation_residue_ge_floor_sub_shared
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T19:05:26.163861+00:00
-- url     : https://prove2.me/theorems/1d501214-833b-4547-9496-0bbf1362e258
-- title:
--   A novel increment bounds residue by floor minus sharing
-- statement:
--   Assume guarded MarginalFloor for the shared family-cost data. If r is tested and support-novel over S union T and both that union and its insertion of r are ledger-admissible, the cost of the insertion minus the two separate family costs is at least epsilon minus sharedCost(S,T). No sign for sharedCost is assumed.
-- source:
--   Theorems/Thm_APFB05_relation_residue.lean:52

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

theorem APFB05.relation_residue_ge_floor_sub_shared
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (S T : Finset (D g)) (r : D g) (htested : tested g r)
    (hU : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (S ∪ T))
    (hW : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert r (S ∪ T)))
    (hnew : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (S ∪ T) r) :
    epsilon g - sharedCost (familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g)) S T ≤
      familyCost (wholeResource g) (calibration g) (maintained g)
          (sufficient g) (usesToRealize g) (insert r (S ∪ T)) -
        familyCost (wholeResource g) (calibration g) (maintained g)
          (sufficient g) (usesToRealize g) S -
        familyCost (wholeResource g) (calibration g) (maintained g)
          (sufficient g) (usesToRealize g) T := by sorry
