-- Prove2me | Theorems.Thm_BookProof_HermiteCarleman_sum_range_of_disjoint
-- name    : BookProof.HermiteCarleman.sum_range_of_disjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:23:50.40314+00:00
-- url     : https://prove2.me/theorems/c8b5e333-6d44-45d0-9921-36ed7363fe90
-- title:
--   `BookProof.HermiteCarleman.sum_range_of_disjoint` {B : ℝ} (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (G : ℕ → Finset (Fin d →₀ ℕ)) (hd : ∀ M N :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteCarlemanEsa`.
--
--   `BookProof.HermiteCarleman.sum_range_of_disjoint` {B : ℝ} (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (G : ℕ → Finset (Fin d →₀ ℕ)) (hd : ∀ M N : ℕ, M ≠ N → Disjoint (G M) (G N)) (M : ℕ) : ∑ N ∈ Finset.range M, ∑ a ∈ G N, ‖u a‖ ^ 2 ≤ B
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteCarleman.sum_range_of_disjoint`.

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.sum_range_of_disjoint
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

theorem BookProof.HermiteCarleman.sum_range_of_disjoint {B : ℝ}
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B)
    (G : ℕ → Finset (Fin d →₀ ℕ)) (hd : ∀ M N : ℕ, M ≠ N → Disjoint (G M) (G N)) (M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ a ∈ G N, ‖u a‖ ^ 2 ≤ B := by sorry
