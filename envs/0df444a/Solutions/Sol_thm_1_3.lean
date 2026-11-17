-- Prove2me | solution 1 for thm_1_3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:28:49.353991+00:00
-- url     : https://prove2.me/submissions/ecdb0360-6186-4a45-a03b-16afb3bed09e

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_3_F001
import Mathlib.Tactic
import Theorems.Thm_rsIntegral_integrator_add
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Pointwise
open Finset Set
noncomputable section

theorem solution {f α₁ α₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : RSIntegrable f α₁ a b)
    (h₂ : RSIntegrable f α₂ a b) :
    ∃ hsum : RSIntegrable f (fun x => α₁ x + α₂ x) a b,
      rsIntegral f (fun x => α₁ x + α₂ x) a b hsum =
        rsIntegral f α₁ a b h₁ + rsIntegral f α₂ a b h₂ := by
  exact ⟨rsIntegrable_integrator_add h₁ h₂, rsIntegral_integrator_add h₁ h₂⟩
