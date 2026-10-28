-- Prove2me | Theorems.Thm_BookProof_HermiteCarleman_flux_identity
-- name    : BookProof.HermiteCarleman.flux_identity
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:22:46.578081+00:00
-- url     : https://prove2.me/theorems/1c57bb98-6d97-45ac-bcc3-0c81aa02ed3e
-- title:
--   `BookProof.HermiteCarleman.flux_identity` (hrec : LadderRec u lam amp z) (N : ℕ) : z.im * (∑ a ∈ cube d N, ‖u a‖ ^ 2) = ∑ i, (∑ a ∈ face d N i, rterm u amp i a).im
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteCarlemanEsa`.
--
--   `BookProof.HermiteCarleman.flux_identity` (hrec : LadderRec u lam amp z) (N : ℕ) : z.im * (∑ a ∈ cube d N, ‖u a‖ ^ 2) = ∑ i, (∑ a ∈ face d N i, rterm u amp i a).im
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteCarleman.flux_identity`.

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.flux_identity
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterHermiteCarlemanEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.HermiteCarleman



open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {u : (Fin d →₀ ℕ) → ℂ} {lam : (Fin d →₀ ℕ) → ℝ} {amp : Fin d → ℂ} {z : ℂ}

theorem BookProof.HermiteCarleman.flux_identity (hrec : LadderRec u lam amp z) (N : ℕ) :
    z.im * (∑ a ∈ cube d N, ‖u a‖ ^ 2)
      = ∑ i, (∑ a ∈ face d N i, rterm u amp i a).im := by sorry
