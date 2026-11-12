-- Prove2me | Theorems.Thm_BookProof_SmFockEsa_smFockHam_esa
-- name    : BookProof.SmFockEsa.smFockHam_esa
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-11T07:37:30.681435+00:00
-- url     : https://prove2.me/theorems/1d0e2c64-ad9f-4d0f-8c5a-966583a99bc5
-- title:
--   `BookProof.SmFockEsa.smFockHam_esa` (P : SmParams) : EssentiallySelfAdjointOn smFockCore (smFockHam P)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmFockEsa`.
--
--   `BookProof.SmFockEsa.smFockHam_esa` (P : SmParams) : EssentiallySelfAdjointOn smFockCore (smFockHam P)
--
--   Formalization note: Lean 4 identifier `BookProof.SmFockEsa.smFockHam_esa`.

-- Generated from ChapterSmFockEsa.lean — theorem BookProof.SmFockEsa.smFockHam_esa
import Definitions.Def_ChapterSmFockEsa
import Definitions.Def_ChapterFarisLavineCore
import Mathlib

open MvPolynomial
open BookProof.FarisLavine
open BookProof.SmOuterFock BookProof.SmHamiltonian

noncomputable section

theorem BookProof.SmFockEsa.smFockHam_esa (P : SmParams) :
    EssentiallySelfAdjointOn smFockCore (smFockHam P) := by sorry
