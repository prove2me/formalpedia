-- Prove2me | Theorems.Thm_BookProof_NavierStokesEulerian_nsBrst_not_hermitian
-- name    : BookProof.NavierStokesEulerian.nsBrst_not_hermitian
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:40:13.103977+00:00
-- url     : https://prove2.me/theorems/55f46e1d-a6d1-4720-acdb-5c0b9fca1c39
-- title:
--   `BookProof.NavierStokesEulerian.nsBrst_not_hermitian` {n : ℕ} (d : NSTruncation n) (h : nsDivergence d ≠ 0) : (nsBrstCharge d)ᴴ ≠ nsBrstCharge d
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesEulerian`.
--
--   `BookProof.NavierStokesEulerian.nsBrst_not_hermitian` {n : ℕ} (d : NSTruncation n) (h : nsDivergence d ≠ 0) : (nsBrstCharge d)ᴴ ≠ nsBrstCharge d
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesEulerian.nsBrst_not_hermitian`.

-- Generated from ChapterNavierStokesEulerian.lean — theorem BookProof.NavierStokesEulerian.nsBrst_not_hermitian
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.GhostField
open BookProof.NavierStokesEulerian



open BookProof.NavierStokesFlow Matrix
open BookProof.NavierStokesFlow

theorem BookProof.NavierStokesEulerian.nsBrst_not_hermitian {n : ℕ} (d : NSTruncation n) (h : nsDivergence d ≠ 0) :
    (nsBrstCharge d)ᴴ ≠ nsBrstCharge d := by sorry
