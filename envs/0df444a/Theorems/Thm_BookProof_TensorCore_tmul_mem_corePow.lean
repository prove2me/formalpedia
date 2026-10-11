-- Prove2me | Theorems.Thm_BookProof_TensorCore_tmul_mem_corePow
-- name    : BookProof.TensorCore.tmul_mem_corePow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:04:42.745836+00:00
-- url     : https://prove2.me/theorems/fd58ac73-b3ec-4984-a019-a25b4086330e
-- title:
--   `BookProof.TensorCore.tmul_mem_corePow` {n : ℕ} {a : D₂} (ha : (a : Hs.carrier) ∈ D) {b : ((domSpace Hs D₂).pow n)} (hb : b ∈ corePow Hs D₂ D n) : a ⊗ₜ[ℂ] b ∈ corePow Hs D₂...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorGraphCore`.
--
--   `BookProof.TensorCore.tmul_mem_corePow` {n : ℕ} {a : D₂} (ha : (a : Hs.carrier) ∈ D) {b : ((domSpace Hs D₂).pow n)} (hb : b ∈ corePow Hs D₂ D n) : a ⊗ₜ[ℂ] b ∈ corePow Hs D₂ D (n + 1)
--
--   Formalization note: Lean 4 identifier `BookProof.TensorCore.tmul_mem_corePow`.

-- Generated from ChapterTensorGraphCore.lean — theorem BookProof.TensorCore.tmul_mem_corePow
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TensorCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

theorem BookProof.TensorCore.tmul_mem_corePow {n : ℕ} {a : D₂} (ha : (a : Hs.carrier) ∈ D)
    {b : ((domSpace Hs D₂).pow n)} (hb : b ∈ corePow Hs D₂ D n) :
    a ⊗ₜ[ℂ] b ∈ corePow Hs D₂ D (n + 1) := by sorry
