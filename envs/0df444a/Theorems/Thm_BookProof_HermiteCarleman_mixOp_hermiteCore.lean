-- Prove2me | Theorems.Thm_BookProof_HermiteCarleman_mixOp_hermiteCore
-- name    : BookProof.HermiteCarleman.mixOp_hermiteCore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:25:24.892674+00:00
-- url     : https://prove2.me/theorems/0eb5d0c1-b84e-4582-b9cf-572959294369
-- title:
--   `BookProof.HermiteCarleman.mixOp_hermiteCore` (c b b' : Fin d → ℝ) (a : Fin d →₀ ℕ) : mixOp c b b' (hermiteCore a) = ((quadSymbol c a : ℝ) : ℂ) • hermiteMvLp a + ∑ i, ((foAmp b b'
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteCarlemanEsa`.
--
--   `BookProof.HermiteCarleman.mixOp_hermiteCore` (c b b' : Fin d → ℝ) (a : Fin d →₀ ℕ) : mixOp c b b' (hermiteCore a) = ((quadSymbol c a : ℝ) : ℂ) • hermiteMvLp a + ∑ i, ((foAmp b b' i * ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ)) • hermiteMvLp (a + Finsupp.single i 1) + ((starRingEnd ℂ) (foAmp b b' i) * ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ)) • hermiteMvLp (a - Finsupp.single i 1))
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteCarleman.mixOp_hermiteCore`.

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.mixOp_hermiteCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterHermiteCarlemanEsa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore
open BookProof.HermiteRelative
open BookProof.HyperbolicQuadratic
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

theorem BookProof.HermiteCarleman.mixOp_hermiteCore (c b b' : Fin d → ℝ) (a : Fin d →₀ ℕ) :
    mixOp c b b' (hermiteCore a)
      = ((quadSymbol c a : ℝ) : ℂ) • hermiteMvLp a
        + ∑ i, ((foAmp b b' i * ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ))
                  • hermiteMvLp (a + Finsupp.single i 1)
                + ((starRingEnd ℂ) (foAmp b b' i) * ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ))
                  • hermiteMvLp (a - Finsupp.single i 1)) := by sorry
