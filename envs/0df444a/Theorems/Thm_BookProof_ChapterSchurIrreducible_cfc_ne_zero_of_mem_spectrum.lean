-- Prove2me | Theorems.Thm_BookProof_ChapterSchurIrreducible_cfc_ne_zero_of_mem_spectrum
-- name    : BookProof.ChapterSchurIrreducible.cfc_ne_zero_of_mem_spectrum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:01:33.104299+00:00
-- url     : https://prove2.me/theorems/8190a00a-1343-4104-8861-a65185427a01
-- title:
--   `BookProof.ChapterSchurIrreducible.cfc_ne_zero_of_mem_spectrum` [Nontrivial V] {T : V →L[ℂ] V} (hT : IsSelfAdjoint T) {f : ℝ → ℝ} (hf : Continuous f) {p : ℝ} (hp : p ∈ spectrum ℝ T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurIrreducible`.
--
--   `BookProof.ChapterSchurIrreducible.cfc_ne_zero_of_mem_spectrum` [Nontrivial V] {T : V →L[ℂ] V} (hT : IsSelfAdjoint T) {f : ℝ → ℝ} (hf : Continuous f) {p : ℝ} (hp : p ∈ spectrum ℝ T) (hfp : f p ≠ 0) : cfc f T ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurIrreducible.cfc_ne_zero_of_mem_spectrum`.

-- Generated from ChapterSchurIrreducible.lean — theorem BookProof.ChapterSchurIrreducible.cfc_ne_zero_of_mem_spectrum
import Definitions.Def_ChapterA
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
open BookProof.ChapterSchurIrreducible


open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurIrreducible.cfc_ne_zero_of_mem_spectrum [Nontrivial V] {T : V →L[ℂ] V} (hT : IsSelfAdjoint T)
    {f : ℝ → ℝ} (hf : Continuous f) {p : ℝ} (hp : p ∈ spectrum ℝ T) (hfp : f p ≠ 0) :
    cfc f T ≠ 0 := by sorry
