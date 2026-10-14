-- Prove2me | Theorems.Thm_BookProof_SecondQuantizationCore_exists_ne_zero_mem_dGammaCoreDomain
-- name    : BookProof.SecondQuantizationCore.exists_ne_zero_mem_dGammaCoreDomain
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:08:52.506716+00:00
-- url     : https://prove2.me/theorems/a2943863-8264-4862-8c57-39c1000402af
-- title:
--   `BookProof.SecondQuantizationCore.exists_ne_zero_mem_dGammaCoreDomain` (hD : D ≤ D₂) {a : Hs.carrier} (haD : a ∈ D) (ha0 : a ≠ 0) : ∃ f ∈ dsCore (fun n : ℕ => fockSectorCore Hs D₂
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSecondQuantizationCoreEsa`.
--
--   `BookProof.SecondQuantizationCore.exists_ne_zero_mem_dGammaCoreDomain` (hD : D ≤ D₂) {a : Hs.carrier} (haD : a ∈ D) (ha0 : a ≠ 0) : ∃ f ∈ dsCore (fun n : ℕ => fockSectorCore Hs D₂ D n), f ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.SecondQuantizationCore.exists_ne_zero_mem_dGammaCoreDomain`.

-- Generated from ChapterSecondQuantizationCoreEsa.lean — theorem BookProof.SecondQuantizationCore.exists_ne_zero_mem_dGammaCoreDomain
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterTensorGraphCore
open BookProof.DirectSumEsa
open BookProof.TensorCore
open BookProof.SecondQuantizationCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore BookProof.DirectSumEsa

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.SecondQuantizationCore.exists_ne_zero_mem_dGammaCoreDomain (hD : D ≤ D₂) {a : Hs.carrier} (haD : a ∈ D)
    (ha0 : a ≠ 0) :
    ∃ f ∈ dsCore (fun n : ℕ => fockSectorCore Hs D₂ D n), f ≠ 0 := by sorry
