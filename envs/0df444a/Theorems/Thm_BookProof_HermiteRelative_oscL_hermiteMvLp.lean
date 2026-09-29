-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_oscL_hermiteMvLp
-- name    : BookProof.HermiteRelative.oscL_hermiteMvLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:50:33.695988+00:00
-- url     : https://prove2.me/theorems/6787e176-743f-4d30-98d7-66089a0b9ff0
-- title:
--   The Lean 4 theorem `oscL_hermiteMvLp` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `oscL_hermiteMvLp` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.oscL_hermiteMvLp
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
open BookProof.HermiteRelative









open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}





variable {d : ℕ}

set_option maxHeartbeats 1000000 in
-- the `L²` coercions of the Gauss–polynomial core make this defeq check expensive

theorem BookProof.HermiteRelative.oscL_hermiteMvLp (i : Fin d) (a : Fin d →₀ ℕ)
    (h : hermiteMvLp a ∈ polyGaussCore (d := d)) :
    oscL i ⟨hermiteMvLp a, h⟩ = (((a i : ℝ) + 1/2 : ℝ) : ℂ) • hermiteMvLp a := by sorry
