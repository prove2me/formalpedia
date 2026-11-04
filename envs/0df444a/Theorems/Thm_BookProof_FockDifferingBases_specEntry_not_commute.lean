-- Prove2me | Theorems.Thm_BookProof_FockDifferingBases_specEntry_not_commute
-- name    : BookProof.FockDifferingBases.specEntry_not_commute
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T04:50:26.89875+00:00
-- url     : https://prove2.me/theorems/090c8ce4-c5c9-4944-b327-3f91eb0b6de6
-- title:
--   `BookProof.FockDifferingBases.specEntry_not_commute` : matMul (specEntry (1 : ℝ) (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0)) (specEntry (1 : ℝ) (fun _ : Fin 2 => (1 : ℂ))) ≠ m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockDifferingBasesEsa`.
--
--   `BookProof.FockDifferingBases.specEntry_not_commute` : matMul (specEntry (1 : ℝ) (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0)) (specEntry (1 : ℝ) (fun _ : Fin 2 => (1 : ℂ))) ≠ matMul (specEntry (1 : ℝ) (fun _ : Fin 2 => (1 : ℂ))) (specEntry (1 : ℝ) (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0))
--
--   Formalization note: Lean 4 identifier `BookProof.FockDifferingBases.specEntry_not_commute`.

-- Generated from ChapterFockDifferingBasesEsa.lean — theorem BookProof.FockDifferingBases.specEntry_not_commute
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterFockQuadraticEsa
import Mathlib
import Definitions.Def_ChapterFockDifferingBasesEsa
import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterFockWeightedSchurEsa
import Definitions.Def_ChapterNavierStokesIkebeKato



open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries BookProof.FockQuadratic

noncomputable section

variable {ι κ : Type*} {ω : ι → ℝ}

theorem BookProof.FockDifferingBases.specEntry_not_commute :
    matMul (specEntry (1 : ℝ) (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0))
        (specEntry (1 : ℝ) (fun _ : Fin 2 => (1 : ℂ)))
      ≠ matMul (specEntry (1 : ℝ) (fun _ : Fin 2 => (1 : ℂ)))
        (specEntry (1 : ℝ) (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0)) := by sorry
