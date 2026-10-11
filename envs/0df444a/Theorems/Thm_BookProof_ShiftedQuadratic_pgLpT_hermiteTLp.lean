-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_pgLpT_hermiteTLp
-- name    : BookProof.ShiftedQuadratic.pgLpT_hermiteTLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:26:30.424061+00:00
-- url     : https://prove2.me/theorems/e1db3473-6576-400d-9726-8ac8ad37639b
-- title:
--   `BookProof.ShiftedQuadratic.pgLpT_hermiteTLp` (a k : Vd d) (α : Fin d →₀ ℕ) : pgLpT a k (((hermiteMvNorm α : ℝ) : ℂ)⁻¹ • hermiteMv α) = hermiteTLp a k α
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.pgLpT_hermiteTLp` (a k : Vd d) (α : Fin d →₀ ℕ) : pgLpT a k (((hermiteMvNorm α : ℝ) : ℂ)⁻¹ • hermiteMv α) = hermiteTLp a k α
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.pgLpT_hermiteTLp`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.pgLpT_hermiteTLp
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.ShiftedHermiteCore
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ShiftedQuadratic.pgLpT_hermiteTLp (a k : Vd d) (α : Fin d →₀ ℕ) :
    pgLpT a k (((hermiteMvNorm α : ℝ) : ℂ)⁻¹ • hermiteMv α) = hermiteTLp a k α := by sorry
