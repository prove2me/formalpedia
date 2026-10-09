-- Prove2me | Theorems.Thm_BookProof_ChapterA3_lorentzLie_smul
-- name    : BookProof.ChapterA3.lorentzLie_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:45:51.003184+00:00
-- url     : https://prove2.me/theorems/6df9ccbe-579d-4868-8268-3a7a89e40f6b
-- title:
--   `BookProof.ChapterA3.lorentzLie_smul` {A : Matrix (Fin 4) (Fin 4) ℝ} (c : ℝ) (h : A ∈ LorentzLie) : c • A ∈ LorentzLie
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3e`.
--
--   `BookProof.ChapterA3.lorentzLie_smul` {A : Matrix (Fin 4) (Fin 4) ℝ} (c : ℝ) (h : A ∈ LorentzLie) : c • A ∈ LorentzLie
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.lorentzLie_smul`.

-- Generated from ChapterA3e.lean — theorem BookProof.ChapterA3.lorentzLie_smul
import Mathlib
import Definitions.Def_ChapterA3e
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.lorentzLie_smul {A : Matrix (Fin 4) (Fin 4) ℝ} (c : ℝ)
    (h : A ∈ LorentzLie) : c • A ∈ LorentzLie := by sorry
