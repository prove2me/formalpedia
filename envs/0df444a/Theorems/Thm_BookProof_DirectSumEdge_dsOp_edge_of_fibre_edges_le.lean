-- Prove2me | Theorems.Thm_BookProof_DirectSumEdge_dsOp_edge_of_fibre_edges_le
-- name    : BookProof.DirectSumEdge.dsOp_edge_of_fibre_edges_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:58:18.71704+00:00
-- url     : https://prove2.me/theorems/2f9db108-7543-488e-b61c-6ca1193119e5
-- title:
--   `BookProof.DirectSumEdge.dsOp_edge_of_fibre_edges_le` (H : ∀ i, D i →ₗ[ℂ] G i) (nu : ℝ) (nus : ι → ℝ) (hle : ∀ i, nu ≤ nus i) (hedge : ∀ i (u : D i), nus i * ‖(u : G i)‖...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEdge`.
--
--   `BookProof.DirectSumEdge.dsOp_edge_of_fibre_edges_le` (H : ∀ i, D i →ₗ[ℂ] G i) (nu : ℝ) (nus : ι → ℝ) (hle : ∀ i, nu ≤ nus i) (hedge : ∀ i (u : D i), nus i * ‖(u : G i)‖ ^ 2 ≤ quadForm (H i) u) (x : dsCore D) : nu * ‖(x : lp G 2)‖ ^ 2 ≤ quadForm (dsOp H) x
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEdge.dsOp_edge_of_fibre_edges_le`.

-- Generated from ChapterDirectSumEdge.lean — theorem BookProof.DirectSumEdge.dsOp_edge_of_fibre_edges_le
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterDirectSumEdge
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
open BookProof.DirectSumEsa
open BookProof.DirectSumEdge



open BookProof.FarisLavine BookProof.DirectSumEsa

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)}

theorem BookProof.DirectSumEdge.dsOp_edge_of_fibre_edges_le (H : ∀ i, D i →ₗ[ℂ] G i) (nu : ℝ) (nus : ι → ℝ)
    (hle : ∀ i, nu ≤ nus i)
    (hedge : ∀ i (u : D i), nus i * ‖(u : G i)‖ ^ 2 ≤ quadForm (H i) u) (x : dsCore D) :
    nu * ‖(x : lp G 2)‖ ^ 2 ≤ quadForm (dsOp H) x := by sorry
