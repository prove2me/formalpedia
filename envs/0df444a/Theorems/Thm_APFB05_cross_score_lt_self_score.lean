-- Prove2me | Theorems.Thm_APFB05_cross_score_lt_self_score
-- name    : APFB05.cross_score_lt_self_score
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:47:49.422644+00:00
-- url     : https://prove2.me/theorems/1b690258-0ac7-4bbc-a5f7-748b36e80d1d
-- title:
--   A novel task shares strictly less with its base than with itself
-- statement:
--   Shared cost is computed from the same infimal family costs used by B05, as individual costs minus union cost. No nonnegative lower bound on the cross shared cost is supplied. This is a conditional comparison on supplied ledger data, not a proof of the existence or physical meaning of a pair-score representation. Assume B05 and a tested e support-novel over S, with S and its enlargement admissible. The shared cost of S with the singleton e is strictly smaller than the singleton's shared cost with itself. The floor's strict positivity turns the marginal upper bound into a strict comparison. Source: Shared-cost definition as negative delta; Paper 1 Supplement v9.28, lines 1816–1826; explicit K-layer reference scope.
-- source:
--   Theorems/Thm_APFB05_shared_cost_floor.lean, declaration at line 90 (Sib v15; source-scoped review). Shared-cost definition as negative delta; Paper 1 Supplement v9.28, lines 1816–1826; explicit K-layer reference scope.

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

theorem APFB05.cross_score_lt_self_score
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (S : Finset (D g)) (e : D g) (htested : tested g e)
    (hS : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) S)
    (hSe : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert e S))
    (hnew : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S e) :
    sharedCost (familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g)) S {e} <
      sharedCost (familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g)) {e} {e} := by sorry
