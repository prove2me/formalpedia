-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockContinuum_memLp_conj
-- name    : BookProof.NavierStokesFlow.FockContinuum.memLp_conj
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:18:14.061979+00:00
-- url     : https://prove2.me/theorems/50187688-b783-4818-9f3d-0bb70d53eb00
-- title:
--   `BookProof.NavierStokesFlow.FockContinuum.memLp_conj` {μ : Measure X} {F : X → ℂ} (h : MemLp F 2 μ) : MemLp (fun x => (starRingEnd ℂ) (F x)) 2 μ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockContinuum`.
--
--   `BookProof.NavierStokesFlow.FockContinuum.memLp_conj` {μ : Measure X} {F : X → ℂ} (h : MemLp F 2 μ) : MemLp (fun x => (starRingEnd ℂ) (F x)) 2 μ
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockContinuum.memLp_conj`.

-- Generated from ChapterNavierStokesFockContinuum.lean — theorem BookProof.NavierStokesFlow.FockContinuum.memLp_conj
import Mathlib
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockContinuum


open MeasureTheory



open FullEsa

variable {X : Type*} [MeasurableSpace X]

theorem BookProof.NavierStokesFlow.FockContinuum.memLp_conj {μ : Measure X} {F : X → ℂ} (h : MemLp F 2 μ) :
    MemLp (fun x => (starRingEnd ℂ) (F x)) 2 μ := by sorry
