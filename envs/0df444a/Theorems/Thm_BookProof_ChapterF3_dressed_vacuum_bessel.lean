-- Prove2me | Theorems.Thm_BookProof_ChapterF3_dressed_vacuum_bessel
-- name    : BookProof.ChapterF3.dressed_vacuum_bessel
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-05T13:10:09.136207+00:00
-- url     : https://prove2.me/theorems/4794634c-e5c6-4dbc-90b3-7caf38725e99
-- title:
--   `BookProof.ChapterF3.dressed_vacuum_bessel` {ι : Type*} (x : ι → E') (hx : Orthonormal ℂ x) (v : E') (hv : ‖v‖ = 1) (s : Finset ι) : ∑ j ∈ s, ‖inner (𝕜
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF3`.
--
--   `BookProof.ChapterF3.dressed_vacuum_bessel` {ι : Type*} (x : ι → E') (hx : Orthonormal ℂ x) (v : E') (hv : ‖v‖ = 1) (s : Finset ι) : ∑ j ∈ s, ‖inner (𝕜
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF3.dressed_vacuum_bessel`.

-- Generated from ChapterF3.lean — theorem BookProof.ChapterF3.dressed_vacuum_bessel
import Mathlib
import Definitions.Def_ChapterF3
open BookProof.ChapterF3


open scoped BigOperators
open Polynomial


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']

theorem BookProof.ChapterF3.dressed_vacuum_bessel {ι : Type*} (x : ι → E') (hx : Orthonormal ℂ x)
    (v : E') (hv : ‖v‖ = 1) (s : Finset ι) :
    ∑ j ∈ s, ‖inner (𝕜 := ℂ) (x j) v‖ ^ 2 ≤ 1 := by sorry
