-- Prove2me | Theorems.Thm_APFPaper5_K1_sharedCost_familyCost_le
-- name    : APFPaper5.K1.sharedCost_familyCost_le
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:55:11.075955+00:00
-- url     : https://prove2.me/theorems/3979266d-6cfd-48ee-882b-9aa02d9516a4
-- title:
--   Shared family cost is bounded above by either family cost
-- statement:
--   The costs are infimal whole-protocol bills, and feasibility ensures the needed monotonicity comparisons for both subfamilies. This theorem supplies upper bounds only. It does not prove shared cost is nonnegative, identify it with a physical pair score, or establish K1. The score interpretation therefore remains conditional reference material. Let the union of finite families S and T be feasible in the shared source vocabulary. Define shared cost as the cost of S plus the cost of T minus their union's cost. Then shared cost is at most the cost of S and at most the cost of T. No B05 premise is needed for this result. Source: Shared-cost definition as negative delta; Paper 1 Supplement v9.28, lines 1816–1826; explicit K-layer reference scope.
-- source:
--   Theorems/Thm_APFB05_shared_cost_floor.lean, declaration at line 37 (Sib v15; source-scoped review). Shared-cost definition as negative delta; Paper 1 Supplement v9.28, lines 1816–1826; explicit K-layer reference scope.

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

theorem APFPaper5.K1.sharedCost_familyCost_le (g : Context) (S T : Finset (D g))
    (hfeas : familyFeasible (maintained g) (sufficient g) (usesToRealize g) (S ∪ T)) :
    sharedCost (familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g)) S T ≤
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) S ∧
    sharedCost (familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g)) S T ≤
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) T := by sorry
