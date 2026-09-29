-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_galerkin_flow_transfer
-- name    : BookProof.ChapterSirkTrotterKato.galerkin_flow_transfer
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T07:51:40.175053+00:00
-- url     : https://prove2.me/theorems/7facc531-82a8-4a57-ab7c-402c925cc5dc
-- title:
--   The Lean 4 theorem `galerkin_flow_transfer` in the `ChapterSirkTrotterKatoGalerkin` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `galerkin_flow_transfer` in the `ChapterSirkTrotterKatoGalerkin` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkTrotterKatoGalerkin.lean

-- Generated from ChapterSirkTrotterKatoGalerkin.lean — theorem BookProof.ChapterSirkTrotterKato.galerkin_flow_transfer
import Mathlib
import Definitions.Def_ChapterSirkTrotterKatoGalerkin
import Theorems.Thm_BookProof_HermiteGalerkin_isSelfAdjoint_galerkinCompression
open BookProof.ChapterSirkTrotterKato








noncomputable section

open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterUnitaryTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]










open BookProof.HermiteGalerkin

theorem BookProof.ChapterSirkTrotterKato.galerkin_flow_transfer {A : H →L[ℂ] H} (hA : IsSelfAdjoint A)
    (b : HilbertBasis ℕ ℂ H) (v : H) {T₀ : ℝ} (hT₀ : 0 ≤ T₀) :
    TendstoUniformlyOn
      (fun m t => (ofBounded (galerkinCompression A b m)
        (isSelfAdjoint_galerkinCompression hA b m)).stoneU t v)
      (fun t => (ofBounded A hA).stoneU t v) atTop (Set.Icc (-T₀) T₀) := by sorry
