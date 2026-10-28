-- Prove2me | Theorems.Thm_BookProof_HermiteCarleman_ladder_eq_zero
-- name    : BookProof.HermiteCarleman.ladder_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:24:52.029464+00:00
-- url     : https://prove2.me/theorems/3b6da1e6-7b77-4d86-be47-7ccc340e1d21
-- title:
--   `BookProof.HermiteCarleman.ladder_eq_zero` {B : ℝ} (hz : z.im ≠ 0) (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (hrec : LadderRec u lam amp z) : ∀ a, u a = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteCarlemanEsa`.
--
--   `BookProof.HermiteCarleman.ladder_eq_zero` {B : ℝ} (hz : z.im ≠ 0) (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (hrec : LadderRec u lam amp z) : ∀ a, u a = 0
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteCarleman.ladder_eq_zero`.

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.ladder_eq_zero
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

theorem BookProof.HermiteCarleman.ladder_eq_zero {B : ℝ} (hz : z.im ≠ 0)
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B)
    (hrec : LadderRec u lam amp z) : ∀ a, u a = 0 := by sorry
