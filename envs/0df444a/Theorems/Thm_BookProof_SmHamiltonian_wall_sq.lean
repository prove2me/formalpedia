-- Prove2me | Theorems.Thm_BookProof_SmHamiltonian_wall_sq
-- name    : BookProof.SmHamiltonian.wall_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:09:30.516909+00:00
-- url     : https://prove2.me/theorems/2aa3ba9b-1253-4632-a835-379608fde299
-- title:
--   `BookProof.SmHamiltonian.wall_sq` (P : SmParams) (q : ℝ) : 1 / 2 * (Real.sqrt (P.lam / 2) * (q - P.vev ^ 2)) ^ 2 = P.lam / 4 * (q - P.vev ^ 2) ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmHamiltonian`.
--
--   `BookProof.SmHamiltonian.wall_sq` (P : SmParams) (q : ℝ) : 1 / 2 * (Real.sqrt (P.lam / 2) * (q - P.vev ^ 2)) ^ 2 = P.lam / 4 * (q - P.vev ^ 2) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.SmHamiltonian.wall_sq`.

-- Generated from ChapterSmHamiltonian.lean — theorem BookProof.SmHamiltonian.wall_sq
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterSmHamiltonian
open BookProof.SmHamiltonian



open MvPolynomial
open BookProof.SmOneParticle
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension

noncomputable section

variable {D : ℕ}

theorem BookProof.SmHamiltonian.wall_sq (P : SmParams) (q : ℝ) :
    1 / 2 * (Real.sqrt (P.lam / 2) * (q - P.vev ^ 2)) ^ 2
      = P.lam / 4 * (q - P.vev ^ 2) ^ 2 := by sorry
