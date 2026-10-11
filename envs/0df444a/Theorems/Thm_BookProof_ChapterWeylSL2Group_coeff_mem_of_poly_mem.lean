-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSL2Group_coeff_mem_of_poly_mem
-- name    : BookProof.ChapterWeylSL2Group.coeff_mem_of_poly_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:38:26.864904+00:00
-- url     : https://prove2.me/theorems/381d2aea-d93e-4f19-a9e5-b6471bd8e0aa
-- title:
--   `BookProof.ChapterWeylSL2Group.coeff_mem_of_poly_mem` {W : Submodule ℂ V} {N : ℕ} {c : ℕ → V} (h : ∀ t : ℂ, ∑ k ∈ Finset.range N, t ^ k • c k ∈ W) {k : ℕ} (hk : k < N) : c...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylSL2Group`.
--
--   `BookProof.ChapterWeylSL2Group.coeff_mem_of_poly_mem` {W : Submodule ℂ V} {N : ℕ} {c : ℕ → V} (h : ∀ t : ℂ, ∑ k ∈ Finset.range N, t ^ k • c k ∈ W) {k : ℕ} (hk : k < N) : c k ∈ W
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeylSL2Group.coeff_mem_of_poly_mem`.

-- Generated from ChapterWeylSL2Group.lean — theorem BookProof.ChapterWeylSL2Group.coeff_mem_of_poly_mem
import Definitions.Def_ChapterWeylSl2
import Mathlib
import Definitions.Def_ChapterWeylSL2Group
open BookProof.ChapterWeylSL2Group



open BookProof.ChapterWeylSl2

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

theorem BookProof.ChapterWeylSL2Group.coeff_mem_of_poly_mem {W : Submodule ℂ V} {N : ℕ} {c : ℕ → V}
    (h : ∀ t : ℂ, ∑ k ∈ Finset.range N, t ^ k • c k ∈ W) {k : ℕ} (hk : k < N) : c k ∈ W := by sorry
