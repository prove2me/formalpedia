-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockContinuum_mem_boundedEnergyCore
-- name    : BookProof.NavierStokesFlow.FockContinuum.mem_boundedEnergyCore
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:40:38.485509+00:00
-- url     : https://prove2.me/theorems/7dbc9255-21bf-4b32-baa5-de7e8bad2831
-- title:
--   `BookProof.NavierStokesFlow.FockContinuum.mem_boundedEnergyCore` {μ : Measure X} {g : X → ℝ} {f : Lp ℂ 2 μ} : f ∈ boundedEnergyCore μ g ↔ ∃ n : ℕ, ∀ᵐ x ∂μ, ¬ (|g x| ≤...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockContinuum`.
--
--   `BookProof.NavierStokesFlow.FockContinuum.mem_boundedEnergyCore` {μ : Measure X} {g : X → ℝ} {f : Lp ℂ 2 μ} : f ∈ boundedEnergyCore μ g ↔ ∃ n : ℕ, ∀ᵐ x ∂μ, ¬ (|g x| ≤ (n : ℝ)) → (f : X → ℂ) x = 0
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockContinuum.mem_boundedEnergyCore`.

-- Generated from ChapterNavierStokesFockContinuum.lean — theorem BookProof.NavierStokesFlow.FockContinuum.mem_boundedEnergyCore
import Mathlib
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockContinuum


open MeasureTheory



open FullEsa

variable {X : Type*} [MeasurableSpace X]

theorem BookProof.NavierStokesFlow.FockContinuum.mem_boundedEnergyCore {μ : Measure X} {g : X → ℝ} {f : Lp ℂ 2 μ} :
    f ∈ boundedEnergyCore μ g ↔ ∃ n : ℕ, ∀ᵐ x ∂μ, ¬ (|g x| ≤ (n : ℝ)) → (f : X → ℂ) x = 0 := by sorry
