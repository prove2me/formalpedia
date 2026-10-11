-- Prove2me | Theorems.Thm_BookProof_TensorCore_graphPow_range_le_closure
-- name    : BookProof.TensorCore.graphPow_range_le_closure
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T16:04:39.214118+00:00
-- url     : https://prove2.me/theorems/d33b69b0-20ac-4450-978f-f03808d6719c
-- title:
--   `BookProof.TensorCore.graphPow_range_le_closure` (hcore : IsGraphCore D A) (n : ℕ) : LinearMap.range (graphPow Hs D₂ A n) ≤ (Submodule.map (graphPow Hs D₂ A n) (corePow Hs D₂ D n))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorGraphCore`.
--
--   `BookProof.TensorCore.graphPow_range_le_closure` (hcore : IsGraphCore D A) (n : ℕ) : LinearMap.range (graphPow Hs D₂ A n) ≤ (Submodule.map (graphPow Hs D₂ A n) (corePow Hs D₂ D n)).topologicalClosure
--
--   Formalization note: Lean 4 identifier `BookProof.TensorCore.graphPow_range_le_closure`.

-- Generated from ChapterTensorGraphCore.lean — theorem BookProof.TensorCore.graphPow_range_le_closure
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterGraphCoreTransfer
open BookProof.GraphCore
open BookProof.TensorCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

theorem BookProof.TensorCore.graphPow_range_le_closure (hcore : IsGraphCore D A) (n : ℕ) :
    LinearMap.range (graphPow Hs D₂ A n)
      ≤ (Submodule.map (graphPow Hs D₂ A n) (corePow Hs D₂ D n)).topologicalClosure := by sorry
