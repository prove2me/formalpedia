-- Prove2me | Theorems.Thm_BookProof_SirkCertifiedGap_certified_parity_gap_of_data
-- name    : BookProof.SirkCertifiedGap.certified_parity_gap_of_data
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:35:24.6559+00:00
-- url     : https://prove2.me/theorems/300805b6-97d3-4ef4-a9b5-b2c049b22652
-- title:
--   {T P : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {vE : E} (hvE : ‖vE‖ = 1) (hvEmem : vE ∈ paritySector P 1) {thetaE thetaO deltaE deltaO : ℝ} (hthetaE : rayleigh T vE = thetaE) (hdE : 0 ≤ deltaE) (hOdd :...
-- statement:
--   Lean 4 theorem `BookProof.SirkCertifiedGap.certified_parity_gap_of_data` (module `BookProof.SirkCertifiedGap`), source chapter `BookProof/ChapterSirkCertifiedGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.certified_parity_gap_of_data
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem BookProof.SirkCertifiedGap.certified_parity_gap_of_data {T P : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    {vE : E} (hvE : ‖vE‖ = 1) (hvEmem : vE ∈ paritySector P 1)
    {thetaE thetaO deltaE deltaO : ℝ} (hthetaE : rayleigh T vE = thetaE) (hdE : 0 ≤ deltaE)
    (hOdd : thetaO - deltaO ≤ sectorGround T P (-1)) :
    thetaO - thetaE - (deltaO + deltaE) ≤ sectorGround T P (-1) - sectorGround T P 1 := by sorry
