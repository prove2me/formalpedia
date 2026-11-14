-- Prove2me | Theorems.Thm_APFB05_self_score_ge_floor
-- name    : APFB05.self_score_ge_floor
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:49:26.041195+00:00
-- url     : https://prove2.me/theorems/a32e3440-8631-4658-b2ff-47317d1b2ab2
-- title:
--   A novel singleton has self shared cost at least the floor
-- statement:
--   Shared cost of a family with itself equals its own cost. Nonnegative empty-family cost and the guarded floor yield the stated bound; a zero-cost empty protocol is not assumed. This establishes a conditional numerical inequality, not physical score identification or positivity of a whole pair table. Assume B05 and a tested task d that is support-novel over the empty family. If the empty family and the singleton are both admissible, the singleton's shared cost with itself is at least the context's positive floor. The conclusion uses the same infimal family cost in the shared-cost definition and in the B05 hypothesis. Source: Shared-cost definition as negative delta; Paper 1 Supplement v9.28, lines 1816–1826; explicit K-layer reference scope.
-- source:
--   Theorems/Thm_APFB05_shared_cost_floor.lean, declaration at line 52 (Sib v15; source-scoped review). Shared-cost definition as negative delta; Paper 1 Supplement v9.28, lines 1816–1826; explicit K-layer reference scope.

import Definitions.Def_APF_B05_DeclaredInput_r2
import Definitions.Def_APFPaper5_K1_SharedCost
import Theorems.Thm_APFPaper1_Source_familyCost_nonneg
import Theorems.Thm_APFPaper1_Source_familyCost_mono
import Theorems.Thm_APFPaper5_K1_sharedCost_self
import Theorems.Thm_APFPaper5_K1_sharedCost_le_right
import Theorems.Thm_APFPaper5_K1_sharedCost_le_left
import Theorems.Thm_APFPaper5_K1_sharedCost_nonneg_iff
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_ledger
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_no_joint
import Theorems.Thm_APFPaper5_K1_cost_is_count_times_floor
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

theorem APFB05.self_score_ge_floor
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (d : D g) (htested : tested g d)
    (h0 : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) ∅)
    (hd : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert d ∅))
    (hnew : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) ∅ d) :
    epsilon g ≤ sharedCost (familyCost (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g)) (insert d ∅) (insert d ∅) := by sorry
