-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_inner_rotHermiteLp
-- name    : BookProof.QuadraticRotation.inner_rotHermiteLp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T23:22:05.248778+00:00
-- url     : https://prove2.me/theorems/450e59eb-0b64-4f24-92f0-03134d5551d4
-- title:
--   The Lean 4 theorem `inner_rotHermiteLp` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.QuadraticRotation.inner_rotHermiteLp` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.inner_rotHermiteLp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore
open BookProof.QuadraticRotation



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadraticRotation.inner_rotHermiteLp {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (a b : Fin d →₀ ℕ) :
    (inner ℂ (rotHermiteLp O a) (rotHermiteLp O b) : ℂ)
      = (inner ℂ (hermiteMvLp (d := d) a) (hermiteMvLp (d := d) b) : ℂ) := by sorry
