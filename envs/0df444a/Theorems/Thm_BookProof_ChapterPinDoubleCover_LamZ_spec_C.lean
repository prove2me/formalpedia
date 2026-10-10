-- Prove2me | Theorems.Thm_BookProof_ChapterPinDoubleCover_LamZ_spec_C
-- name    : BookProof.ChapterPinDoubleCover.LamZ_spec_C
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:52:17.192623+00:00
-- url     : https://prove2.me/theorems/69eb4018-82ef-4cdd-8ba2-fcc97e19a1dd
-- title:
--   `BookProof.ChapterPinDoubleCover.LamZ_spec_C` : ∀ S ∈ Omega, ∀ μ : Fin 4, mgamma μ * (Int.castRingHom ℂ).mapMatrix S = (Int.castRingHom ℂ).mapMatrix S * (∑ ν : Fin 4, (LamZ S) μ ν
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPinDoubleCover`.
--
--   `BookProof.ChapterPinDoubleCover.LamZ_spec_C` : ∀ S ∈ Omega, ∀ μ : Fin 4, mgamma μ * (Int.castRingHom ℂ).mapMatrix S = (Int.castRingHom ℂ).mapMatrix S * (∑ ν : Fin 4, (LamZ S) μ ν • mgamma ν)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPinDoubleCover.LamZ_spec_C`.

-- Generated from ChapterPinDoubleCover.lean — theorem BookProof.ChapterPinDoubleCover.LamZ_spec_C
import Mathlib
import Definitions.Def_ChapterPinDoubleCover
import Definitions.Def_ChapterA3
open BookProof.ChapterA3
open BookProof.ChapterPinDoubleCover


open Matrix


open BookProof.ChapterA3
open Classical

theorem BookProof.ChapterPinDoubleCover.LamZ_spec_C :
    ∀ S ∈ Omega, ∀ μ : Fin 4,
      mgamma μ * (Int.castRingHom ℂ).mapMatrix S
        = (Int.castRingHom ℂ).mapMatrix S * (∑ ν : Fin 4, (LamZ S) μ ν • mgamma ν) := by sorry
