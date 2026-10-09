-- Prove2me | Theorems.Thm_BookProof_ChapterE_stochastic_uniform_to_vertex_singular
-- name    : BookProof.ChapterE.stochastic_uniform_to_vertex_singular
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:10:20.253526+00:00
-- url     : https://prove2.me/theorems/b92a2446-6473-49ed-8713-909b3c680043
-- title:
--   `BookProof.ChapterE.stochastic_uniform_to_vertex_singular` (M : Matrix (Fin 2) (Fin 2) ℝ) (hnonneg : ∀ i j, 0 ≤ M i j) (hcol : ∀ j, ∑ i, M i j = 1) (huniform : M *ᵥ ![1 / 2, 1 / 2]
-- statement:
--   Prove the following Lean 4 theorem from `ChapterE`.
--
--   `BookProof.ChapterE.stochastic_uniform_to_vertex_singular` (M : Matrix (Fin 2) (Fin 2) ℝ) (hnonneg : ∀ i j, 0 ≤ M i j) (hcol : ∀ j, ∑ i, M i j = 1) (huniform : M *ᵥ ![1 / 2, 1 / 2] = ![1, 0]) : M.det = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterE.stochastic_uniform_to_vertex_singular`.

-- Generated from ChapterE.lean — theorem BookProof.ChapterE.stochastic_uniform_to_vertex_singular
import Mathlib
import Definitions.Def_ChapterE
open BookProof.ChapterE


open scoped Matrix BigOperators
open Filter
open scoped Topology

theorem BookProof.ChapterE.stochastic_uniform_to_vertex_singular
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hnonneg : ∀ i j, 0 ≤ M i j)
    (hcol : ∀ j, ∑ i, M i j = 1)
    (huniform : M *ᵥ ![1 / 2, 1 / 2] = ![1, 0]) :
    M.det = 0 := by sorry
