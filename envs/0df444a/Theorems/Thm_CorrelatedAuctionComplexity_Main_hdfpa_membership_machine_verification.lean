-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_hdfpa_membership_machine_verification
-- name    : CorrelatedAuctionComplexity.Main.hdfpa_membership_machine_verification
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T08:42:53.434213+00:00
-- url     : https://prove2.me/theorems/4a54f744-2d97-4504-88b8-8bcb9e09fc4f
-- title:
--   Lemma 16 — Polynomial-time verification for HDFPA search
-- statement:
--   Assuming the exact polynomial-time expected-utility evaluator of Lemma 15, both machine-verification obligations for variable-accuracy HDFPA equilibrium search hold. First, there is a polynomial-time checker for an input–candidate pair precisely when the candidate is a canonically encoded rational $\eta$-approximate equilibrium within the prescribed witness bound. Second, there is a polynomial-time decider for the valid-instance language: canonical auction decoding, well-formedness, canonically encoded accuracy, and positivity of that accuracy.
-- source:
--   Chen–Chen–Cui–Pires–Stockwell, STOC 2027 submission #324, Lemma 16 and proof, pp. 20–21; expected-utility computation is Lemma 15, pp. 19–20.

import Definitions.Def_CorrelatedAuctionComplexity_Main_NashFixedSearch

set_option autoImplicit false

theorem CorrelatedAuctionComplexity.Main.hdfpa_membership_machine_verification :
    ExpectedUtilityPolytime →
      (CookPvsNP.checkLang hVariableAccuracy.answer ∈
        CookPvsNP.P (Option (Bool ⊕ Bool))) ∧
      ({s | hVariableAccuracy.valid s} ∈ CookPvsNP.P Bool) := by sorry
