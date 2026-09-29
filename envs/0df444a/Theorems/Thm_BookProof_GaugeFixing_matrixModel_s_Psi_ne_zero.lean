-- Prove2me | Theorems.Thm_BookProof_GaugeFixing_matrixModel_s_Psi_ne_zero
-- name    : BookProof.GaugeFixing.matrixModel_s_Psi_ne_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T15:14:40.251718+00:00
-- url     : https://prove2.me/theorems/a4d5bb09-e5a1-40c6-8b92-4753e9518ffe
-- title:
--   The model gauge-fixing BRST differential of $\Psi$ is nonzero
-- statement:
--   The model gauge-fixing BRST differential of $\Psi$ is nonzero.
--
--   In the concrete matrix model the gauge-fixing Lagrangian evaluates to the identity matrix, $s\Psi = 1$, which in particular is nonzero — so the evaluation identity has non-trivial content.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GaugeFixing.matrixModel_s_Psi_ne_zero` (module `BookProof.GaugeFixing`), line-linked source: `ChapterGaugeFixing.lean` lines 366–367.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeFixing.lean#L366-L367

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.matrixModel_s_Psi_ne_zero
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem BookProof.GaugeFixing.matrixModel_s_Psi_ne_zero : (sTop matrixModel (Psi matrixModel) : Mat2) ≠ 0 := by sorry
