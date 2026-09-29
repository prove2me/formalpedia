-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffHashimoto_polySym_sum
-- name    : BookProof.NavierStokesFlow.DiffHashimoto.polySym_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:51:27.147231+00:00
-- url     : https://prove2.me/theorems/8d67b438-dab8-4357-90d9-9ab437460c52
-- title:
--   The Lean 4 theorem `polySym_sum` in the `ChapterNavierStokesDiffHashimoto` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `polySym_sum` in the `ChapterNavierStokesDiffHashimoto` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDiffHashimoto.lean

-- Generated from ChapterNavierStokesDiffHashimoto.lean — theorem BookProof.NavierStokesFlow.DiffHashimoto.polySym_sum
import Mathlib
import Definitions.Def_ChapterNavierStokesDiffHashimoto
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.DiffHashimoto







open Filter Topology



open MvPolynomial
open BookProof.FarisLavine BookProof.HashimotoShiftInvert BookProof.EsaClosure
open BookProof.HermiteGalerkin
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteRelative
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.DiffHashimoto.polySym_sum {d : ℕ} {ι : Type*} (s : Finset ι)
    (T : ι → Module.End ℂ (MvPolynomial (Fin d) ℂ))
    (hT : ∀ i ∈ s, BookProof.YangMillsHermite.PolySym (T i)) :
    BookProof.YangMillsHermite.PolySym (∑ i ∈ s, T i) := by sorry
