-- Prove2me | Theorems.Thm_APFPaper5_K1_weighted_marginal_ge
-- name    : APFPaper5.K1.weighted_marginal_ge
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:15:10.899209+00:00
-- url     : https://prove2.me/theorems/1c5b3476-f103-4d80-bf5c-a07063be2c49
-- title:
--   A new record raises weighted family cost by its record floor
-- statement:
--   Protocols are finite maintained-record sets, bills sum their weights, sufficient support contains a task's required records, and realization-use evidence is unrestricted. The conclusion is about this explicit model. It does not establish that a physical interface has additive record bills or satisfies the named RECORDS hypothesis. In the finite-record model, give each record a nonnegative weight and each task a finite set of required records. Let eps be a real lower bound for every record weight. If task d is support-novel over S in this model, adding d raises infimal family cost by at least eps. This individual theorem does not require eps to be positive. Source: Paper 1 Supplement v9.28, lines 1787–1790 and 2502–2530; November 12 RECORDS hypothesis ruling.
-- source:
--   Theorems/Thm_APFB05_weighted_record_model.lean, declaration at line 26 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 1787–1790 and 2502–2530; November 12 RECORDS hypothesis ruling.

import Definitions.Def_APF_B05_DeclaredInput_r2
import Theorems.Thm_APFPaper5_K1_familyCost_weighted
import Theorems.Thm_APFPaper5_K1_recordModelCost_eq
import Theorems.Thm_APFPaper5_K1_recordModel_sharedCost
import Theorems.Thm_APFPaper5_K1_recordModel_satisfies_K1

set_option autoImplicit false
open APFPaper1.Source APFPaper5.K1

universe u v
variable {ι : Type u} {Rec : Type v} [DecidableEq Rec] [DecidableEq ι]

theorem APFPaper5.K1.weighted_marginal_ge (w : Rec → NNReal) (fam : ι → Finset Rec) (eps : ℝ)
    (hw : ∀ a, eps ≤ (w a : ℝ)) (S : Finset ι) (d : ι)
    (hnew : supportNovel (D := ι) (P := Finset Rec) (R := Finset Rec) (Record := Rec)
      (fun p => p) (fun r => ∑ a ∈ r, w a) (fun p => (↑p : Set Rec))
      (fun _ sigma e => (↑(fam e) : Set Rec) ⊆ sigma) (fun _ _ _ => True) S d) :
    eps ≤ familyCost (D := ι) (P := Finset Rec) (R := Finset Rec) (Record := Rec)
        (fun p => p) (fun r => ∑ a ∈ r, w a) (fun p => (↑p : Set Rec))
        (fun _ sigma e => (↑(fam e) : Set Rec) ⊆ sigma) (fun _ _ _ => True) (insert d S) -
      familyCost (D := ι) (P := Finset Rec) (R := Finset Rec) (Record := Rec)
        (fun p => p) (fun r => ∑ a ∈ r, w a) (fun p => (↑p : Set Rec))
        (fun _ sigma e => (↑(fam e) : Set Rec) ⊆ sigma) (fun _ _ _ => True) S := by sorry
