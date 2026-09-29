-- Prove2me | solution 1 for mme_stothers_phi233_cyclic_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:18:45.256361+00:00
-- url     : https://prove2.me/submissions/cac53f35-7b45-40f4-8b63-5c28f2ae93ef

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_stothers_fourth_data
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions
import Theorems.Thm_mme_stothers_phi233_cyclic_cofinal_finite_extraction

open MME BigOperators Filter

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 9 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 2 3 3)) tau V := by
  intro V hV hVlt
  obtain ⟨s, loss, hs, hloss, hextract⟩ :=
    mme_stothers_phi233_cyclic_cofinal_finite_extraction
      (K := K) tau htauLower htauUpper V hV hVlt
  exact mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    (cyclicSymmetrization
      (MME.StothersFourth.cwFourthConstituent K 6 2 3 3))
    tau V hV s hs loss hloss hextract
