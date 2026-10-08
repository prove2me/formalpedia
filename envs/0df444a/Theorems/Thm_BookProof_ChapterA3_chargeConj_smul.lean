-- Prove2me | Theorems.Thm_BookProof_ChapterA3_chargeConj_smul
-- name    : BookProof.ChapterA3.chargeConj_smul
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:42:32.239493+00:00
-- url     : https://prove2.me/theorems/8650a3a7-515f-42c1-bbc2-2def52e1a3a5
-- title:
--   `BookProof.ChapterA3.chargeConj_smul` (c : ℂ) (v : Fin 4 → ℂ) : chargeConj (c • v) = conj c • chargeConj v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3b`.
--
--   `BookProof.ChapterA3.chargeConj_smul` (c : ℂ) (v : Fin 4 → ℂ) : chargeConj (c • v) = conj c • chargeConj v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.chargeConj_smul`.

-- Generated from ChapterA3b.lean — theorem BookProof.ChapterA3.chargeConj_smul
import Mathlib
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.chargeConj_smul (c : ℂ) (v : Fin 4 → ℂ) :
    chargeConj (c • v) = conj c • chargeConj v := by sorry
