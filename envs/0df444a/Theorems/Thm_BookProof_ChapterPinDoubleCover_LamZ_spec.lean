-- Prove2me | Theorems.Thm_BookProof_ChapterPinDoubleCover_LamZ_spec
-- name    : BookProof.ChapterPinDoubleCover.LamZ_spec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:51:34.975762+00:00
-- url     : https://prove2.me/theorems/f9264a3f-c8f4-4ce4-8b43-d12a49b8b528
-- title:
--   `BookProof.ChapterPinDoubleCover.LamZ_spec` : ∀ S ∈ Omega, ∀ μ : Fin 4, mgammaZ μ * S = S * (∑ ν : Fin 4, (LamZ S) μ ν • mgammaZ ν)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPinDoubleCover`.
--
--   `BookProof.ChapterPinDoubleCover.LamZ_spec` : ∀ S ∈ Omega, ∀ μ : Fin 4, mgammaZ μ * S = S * (∑ ν : Fin 4, (LamZ S) μ ν • mgammaZ ν)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPinDoubleCover.LamZ_spec`.

-- Generated from ChapterPinDoubleCover.lean — theorem BookProof.ChapterPinDoubleCover.LamZ_spec
import Mathlib
import Definitions.Def_ChapterPinDoubleCover
import Definitions.Def_ChapterA3
open BookProof.ChapterA3
open BookProof.ChapterPinDoubleCover


open Matrix


open BookProof.ChapterA3
open Classical

theorem BookProof.ChapterPinDoubleCover.LamZ_spec :
    ∀ S ∈ Omega, ∀ μ : Fin 4,
      mgammaZ μ * S = S * (∑ ν : Fin 4, (LamZ S) μ ν • mgammaZ ν) := by sorry
