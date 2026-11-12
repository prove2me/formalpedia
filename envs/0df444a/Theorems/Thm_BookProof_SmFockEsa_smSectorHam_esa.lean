-- Prove2me | Theorems.Thm_BookProof_SmFockEsa_smSectorHam_esa
-- name    : BookProof.SmFockEsa.smSectorHam_esa
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-11T07:37:36.832775+00:00
-- url     : https://prove2.me/theorems/85dead3b-6edd-4b21-bec6-4bd5a8cf644d
-- title:
--   `BookProof.SmFockEsa.smSectorHam_esa` (P : SmParams) (n : ℕ) : EssentiallySelfAdjointOn (polyGaussCore (d := n * 163)) (smSectorHam P n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmFockEsa`.
--
--   `BookProof.SmFockEsa.smSectorHam_esa` (P : SmParams) (n : ℕ) : EssentiallySelfAdjointOn (polyGaussCore (d := n * 163)) (smSectorHam P n)
--
--   Formalization note: Lean 4 identifier `BookProof.SmFockEsa.smSectorHam_esa`.

-- Generated from ChapterSmFockEsa.lean — theorem BookProof.SmFockEsa.smSectorHam_esa
import Definitions.Def_ChapterSmFockEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavineCore
import Mathlib

open MvPolynomial
open BookProof.FarisLavine
open BookProof.SmOuterFock BookProof.SmHamiltonian
open BookProof.HermiteProductCore

noncomputable section

theorem BookProof.SmFockEsa.smSectorHam_esa (P : SmParams) (n : ℕ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := n * 163)) (smSectorHam P n) := by sorry
