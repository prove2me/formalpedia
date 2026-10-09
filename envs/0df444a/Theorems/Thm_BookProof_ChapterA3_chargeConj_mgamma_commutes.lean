-- Prove2me | Theorems.Thm_BookProof_ChapterA3_chargeConj_mgamma_commutes
-- name    : BookProof.ChapterA3.chargeConj_mgamma_commutes
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:42:59.559854+00:00
-- url     : https://prove2.me/theorems/2b4eec15-d63a-4ff4-841f-38886ef20259
-- title:
--   `BookProof.ChapterA3.chargeConj_mgamma_commutes` (μ : Fin 4) (v : Fin 4 → ℂ) : chargeConj (mgamma μ *ᵥ v) = mgamma μ *ᵥ chargeConj v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3b`.
--
--   `BookProof.ChapterA3.chargeConj_mgamma_commutes` (μ : Fin 4) (v : Fin 4 → ℂ) : chargeConj (mgamma μ *ᵥ v) = mgamma μ *ᵥ chargeConj v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.chargeConj_mgamma_commutes`.

-- Generated from ChapterA3b.lean — theorem BookProof.ChapterA3.chargeConj_mgamma_commutes
import Mathlib
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.chargeConj_mgamma_commutes (μ : Fin 4) (v : Fin 4 → ℂ) :
    chargeConj (mgamma μ *ᵥ v) = mgamma μ *ᵥ chargeConj v := by sorry
