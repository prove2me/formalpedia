-- Prove2me | solution 1 for upperLowerCommonLimit_integrator_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:20:14.290197+00:00
-- url     : https://prove2.me/submissions/1aa535a1-7bf3-4a4e-a83e-d09098b31486

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_3_F000
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Pointwise
open Finset Set
noncomputable section

private theorem source_upperLowerCommonLimit_integrator_add {a b : ℝ} {f α₁ α₂ : ℝ → ℝ}
    {L₁ L₂ : ℝ}
    (h₁ : UpperLowerCommonLimit a b f α₁ L₁)
    (h₂ : UpperLowerCommonLimit a b f α₂ L₂) :
    UpperLowerCommonLimit a b f (fun x => α₁ x + α₂ x) (L₁ + L₂) := by
  rcases h₁ with ⟨hs₁, hlim₁⟩
  rcases h₂ with ⟨hs₂, hlim₂⟩
  refine ⟨sourceHypotheses_integrator_add hs₁ hs₂, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlim₁ (eps / 2) hhalf with ⟨δ₁, hδ₁, H₁⟩
  rcases hlim₂ (eps / 2) hhalf with ⟨δ₂, hδ₂, H₂⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro P hmesh
  have hmesh₁ : P.mesh < δ₁ := lt_of_lt_of_le hmesh (min_le_left δ₁ δ₂)
  have hmesh₂ : P.mesh < δ₂ := lt_of_lt_of_le hmesh (min_le_right δ₁ δ₂)
  have hP₁ := H₁ P hmesh₁
  have hP₂ := H₂ P hmesh₂
  constructor
  · have hadd :
        upperSum P f (fun x => α₁ x + α₂ x) - (L₁ + L₂) =
          (upperSum P f α₁ - L₁) + (upperSum P f α₂ - L₂) := by
      rw [upperSum_integrator_add]
      ring
    calc
      |upperSum P f (fun x => α₁ x + α₂ x) - (L₁ + L₂)| =
          |(upperSum P f α₁ - L₁) + (upperSum P f α₂ - L₂)| := by rw [hadd]
      _ ≤ |upperSum P f α₁ - L₁| + |upperSum P f α₂ - L₂| := abs_add_le _ _
      _ < eps := by
        have hlt :
            |upperSum P f α₁ - L₁| + |upperSum P f α₂ - L₂| <
              eps / 2 + eps / 2 := add_lt_add hP₁.1 hP₂.1
        simpa using hlt
  · have hadd :
        lowerSum P f (fun x => α₁ x + α₂ x) - (L₁ + L₂) =
          (lowerSum P f α₁ - L₁) + (lowerSum P f α₂ - L₂) := by
      rw [lowerSum_integrator_add]
      ring
    calc
      |lowerSum P f (fun x => α₁ x + α₂ x) - (L₁ + L₂)| =
          |(lowerSum P f α₁ - L₁) + (lowerSum P f α₂ - L₂)| := by rw [hadd]
      _ ≤ |lowerSum P f α₁ - L₁| + |lowerSum P f α₂ - L₂| := abs_add_le _ _
      _ < eps := by
        have hlt :
            |lowerSum P f α₁ - L₁| + |lowerSum P f α₂ - L₂| <
              eps / 2 + eps / 2 := add_lt_add hP₁.2 hP₂.2
        simpa using hlt

theorem solution {a b : ℝ} {f α₁ α₂ : ℝ → ℝ}
    {L₁ L₂ : ℝ}
    (h₁ : UpperLowerCommonLimit a b f α₁ L₁)
    (h₂ : UpperLowerCommonLimit a b f α₂ L₂) :
    UpperLowerCommonLimit a b f (fun x => α₁ x + α₂ x) (L₁ + L₂) := by
  exact source_upperLowerCommonLimit_integrator_add h₁ h₂
