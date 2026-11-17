-- Prove2me | solution 1 for rsIntegral_integrator_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:27:13.569911+00:00
-- url     : https://prove2.me/submissions/88bf8334-83d7-4475-94d6-fe7c8ce3b232

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_3_F001
import Mathlib.Tactic
import Theorems.Thm_taggedCommonLimit_unique
import Theorems.Thm_taggedCommonLimit_integrator_add
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Pointwise
open Finset Set
noncomputable section

theorem solution {f α₁ α₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : RSIntegrable f α₁ a b)
    (h₂ : RSIntegrable f α₂ a b) :
  rsIntegral f (fun x => α₁ x + α₂ x) a b (rsIntegrable_integrator_add h₁ h₂) =
    rsIntegral f α₁ a b h₁ + rsIntegral f α₂ a b h₂ := by
  exact taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_integrator_add h₁ h₂))
    (taggedCommonLimit_integrator_add (rsIntegral_spec h₁) (rsIntegral_spec h₂))
