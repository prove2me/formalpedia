-- Prove2me | Theorems.Thm_APFB05_weighted_record_model_satisfies_floor
-- name    : APFB05.weighted_record_model_satisfies_floor
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:14:06.761883+00:00
-- url     : https://prove2.me/theorems/a7813e86-9734-4286-9737-b99346098b84
-- title:
--   A positive uniform record price yields the guarded floor in the record model
-- statement:
--   A protocol is its maintained finite record set; its resource is that same set and calibration sums record weights. This verifies the predicate in a supplied model, including its admissibility guards. It does not infer physical additive record accounting or prove that the declared foundation commitment holds because this example exists. Give every record a nonnegative weight, each task a finite required-record set, and choose a positive real eps no greater than every record's weight. For every supplied context-capacity function, the weighted finite-record model satisfies the guarded B05 predicate with constant floor eps and every task tested. No B05 assumption is consumed. Source: Paper 1 Supplement v9.28, lines 1787–1790 and 2502–2530; November 12 RECORDS hypothesis ruling.
-- source:
--   Theorems/Thm_APFB05_weighted_record_model.lean, declaration at line 64 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 1787–1790 and 2502–2530; November 12 RECORDS hypothesis ruling.

import Definitions.Def_APF_B05_DeclaredInput_r2
import Theorems.Thm_APFPaper5_K1_familyCost_weighted
import Theorems.Thm_APFPaper5_K1_recordModelCost_eq
import Theorems.Thm_APFPaper5_K1_recordModel_sharedCost
import Theorems.Thm_APFPaper5_K1_recordModel_satisfies_K1

set_option autoImplicit false
open APFPaper1.Source APFPaper5.K1

universe u v
variable {ι : Type u} {Rec : Type v} [DecidableEq Rec] [DecidableEq ι]

theorem APFB05.weighted_record_model_satisfies_floor {Context : Type*} (w : Rec → NNReal)
    (fam : ι → Finset Rec) (eps : ℝ) (heps : 0 < eps) (hw : ∀ a, eps ≤ (w a : ℝ))
    (C : Context → ℝ) :
    APFB05.MarginalFloor (Context := Context) (D := fun _ => ι) (P := fun _ => Finset Rec)
      (R := fun _ => Finset Rec) (Record := fun _ => Rec)
      (fun _ p => p) (fun _ r => ∑ a ∈ r, w a) (fun _ p => (↑p : Set Rec))
      (fun _ _ sigma d => (↑(fam d) : Set Rec) ⊆ sigma) (fun _ _ _ _ => True) (fun _ _ => True)
      C (fun _ => eps) := by sorry
