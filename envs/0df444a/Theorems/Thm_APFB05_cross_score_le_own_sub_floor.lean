-- Prove2me | Theorems.Thm_APFB05_cross_score_le_own_sub_floor
-- name    : APFB05.cross_score_le_own_sub_floor
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:47:11.301573+00:00
-- url     : https://prove2.me/theorems/108687ea-0955-41ba-ab7a-bdc4ae3a5d6e
-- title:
--   A novel task shares at most its own cost minus one floor
-- statement:
--   Every family cost uses the same shared source protocol and record arguments. The theorem is an upper bound derived from one guarded marginal inequality. It neither supplies a lower bound on shared cost nor identifies this quantity with a nonnegative physical pair number or a K1 form. Assume B05, an admissible S, a tested task e support-novel over S, and admissibility after adding e. Then the shared cost of S and the singleton e is at most the singleton's own cost minus the context's floor. Shared cost means the sum of the two individual family costs less the cost of their union. Source: Shared-cost definition as negative delta; Paper 1 Supplement v9.28, lines 1816–1826; explicit K-layer reference scope.
-- source:
--   Theorems/Thm_APFB05_shared_cost_floor.lean, declaration at line 70 (Sib v15; source-scoped review). Shared-cost definition as negative delta; Paper 1 Supplement v9.28, lines 1816–1826; explicit K-layer reference scope.

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

theorem APFB05.cross_score_le_own_sub_floor
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
        (sufficient g) (usesToRealize g)) S {e} ≤
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) {e} - epsilon g := by sorry
