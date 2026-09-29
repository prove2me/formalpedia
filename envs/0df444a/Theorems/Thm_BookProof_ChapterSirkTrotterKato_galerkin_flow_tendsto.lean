-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_galerkin_flow_tendsto
-- name    : BookProof.ChapterSirkTrotterKato.galerkin_flow_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T07:51:56.132831+00:00
-- url     : https://prove2.me/theorems/85af7771-6f0e-4cd3-8af7-a593658ce25f
-- title:
--   The Lean 4 theorem `galerkin_flow_tendsto` in the `ChapterSirkTrotterKatoGalerkin` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `galerkin_flow_tendsto` in the `ChapterSirkTrotterKatoGalerkin` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkTrotterKatoGalerkin.lean

-- Generated from ChapterSirkTrotterKatoGalerkin.lean — theorem BookProof.ChapterSirkTrotterKato.galerkin_flow_tendsto
import Mathlib
import Definitions.Def_ChapterSirkTrotterKatoGalerkin
import Theorems.Thm_BookProof_HermiteGalerkin_isSelfAdjoint_galerkinCompression
open BookProof.ChapterSirkTrotterKato








noncomputable section

open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterUnitaryTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]










open BookProof.HermiteGalerkin

theorem BookProof.ChapterSirkTrotterKato.galerkin_flow_tendsto {A : H →L[ℂ] H} (hA : IsSelfAdjoint A)
    (b : HilbertBasis ℕ ℂ H) (v : H) (t : ℝ) :
    Tendsto (fun m => (ofBounded (galerkinCompression A b m)
      (isSelfAdjoint_galerkinCompression hA b m)).stoneU t v) atTop
      (𝓝 ((ofBounded A hA).stoneU t v)) := by sorry
