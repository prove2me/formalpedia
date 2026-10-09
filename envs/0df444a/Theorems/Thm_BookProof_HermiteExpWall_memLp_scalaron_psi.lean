-- Prove2me | Theorems.Thm_BookProof_HermiteExpWall_memLp_scalaron_psi
-- name    : BookProof.HermiteExpWall.memLp_scalaron_psi
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:10:47.032967+00:00
-- url     : https://prove2.me/theorems/ca1231f8-2b39-4c7b-a50f-476880f8b74d
-- title:
--   `BookProof.HermiteExpWall.memLp_scalaron_psi` (M alpha : ℝ) (hM : 0 < M) (N : ℕ) : MemLp (fun x => starobinskyV M alpha x * psi N x) 2 volume
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteExpWall`.
--
--   `BookProof.HermiteExpWall.memLp_scalaron_psi` (M alpha : ℝ) (hM : 0 < M) (N : ℕ) : MemLp (fun x => starobinskyV M alpha x * psi N x) 2 volume
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteExpWall.memLp_scalaron_psi`.

-- Generated from ChapterHermiteExpWall.lean — theorem BookProof.HermiteExpWall.memLp_scalaron_psi
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterHermiteProductCore
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterSirkFinitePrecision
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.GhostField
open BookProof.QgHermiteCore
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval
open BookProof.Starobinsky
open BookProof.HermiteExpWall



open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore

noncomputable section

theorem BookProof.HermiteExpWall.memLp_scalaron_psi (M alpha : ℝ) (hM : 0 < M) (N : ℕ) :
    MemLp (fun x => starobinskyV M alpha x * psi N x) 2 volume := by sorry
