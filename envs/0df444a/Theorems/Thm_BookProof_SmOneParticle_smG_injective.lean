-- Prove2me | Theorems.Thm_BookProof_SmOneParticle_smG_injective
-- name    : BookProof.SmOneParticle.smG_injective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:14:04.093994+00:00
-- url     : https://prove2.me/theorems/c23b3958-c598-4ac7-8cc7-967702e15749
-- title:
--   `BookProof.SmOneParticle.smG_injective` : Function.Injective fun p : Fin 8 × Fin 3 => smG p.1 p.2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmOneParticle`.
--
--   `BookProof.SmOneParticle.smG_injective` : Function.Injective fun p : Fin 8 × Fin 3 => smG p.1 p.2
--
--   Formalization note: Lean 4 identifier `BookProof.SmOneParticle.smG_injective`.

-- Generated from ChapterSmOneParticle.lean — theorem BookProof.SmOneParticle.smG_injective
import Mathlib
import Definitions.Def_ChapterSmOneParticle
open BookProof.SmOneParticle

theorem BookProof.SmOneParticle.smG_injective : Function.Injective fun p : Fin 8 × Fin 3 => smG p.1 p.2 := by sorry
