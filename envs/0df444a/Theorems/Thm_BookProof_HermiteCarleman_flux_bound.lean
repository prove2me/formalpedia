-- Prove2me | Theorems.Thm_BookProof_HermiteCarleman_flux_bound
-- name    : BookProof.HermiteCarleman.flux_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:23:25.334809+00:00
-- url     : https://prove2.me/theorems/7939b454-d958-45dc-ab51-dfca941be367
-- title:
--   `BookProof.HermiteCarleman.flux_bound` (N : ℕ) (i : Fin d) : |(∑ a ∈ face d N i, rterm u amp i a).im| ≤ Real.sqrt ((N : ℝ) + 1) * (‖amp i‖ * ((∑ a ∈ face d N i, (‖u a‖ ^ 2...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteCarlemanEsa`.
--
--   `BookProof.HermiteCarleman.flux_bound` (N : ℕ) (i : Fin d) : |(∑ a ∈ face d N i, rterm u amp i a).im| ≤ Real.sqrt ((N : ℝ) + 1) * (‖amp i‖ * ((∑ a ∈ face d N i, (‖u a‖ ^ 2 + ‖u (a + Finsupp.single i 1)‖ ^ 2)) / 2))
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteCarleman.flux_bound`.

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.flux_bound
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

theorem BookProof.HermiteCarleman.flux_bound (N : ℕ) (i : Fin d) :
    |(∑ a ∈ face d N i, rterm u amp i a).im|
      ≤ Real.sqrt ((N : ℝ) + 1) *
        (‖amp i‖ * ((∑ a ∈ face d N i,
          (‖u a‖ ^ 2 + ‖u (a + Finsupp.single i 1)‖ ^ 2)) / 2)) := by sorry
