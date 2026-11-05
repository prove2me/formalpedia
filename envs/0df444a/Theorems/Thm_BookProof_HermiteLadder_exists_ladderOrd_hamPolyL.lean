-- Prove2me | Theorems.Thm_BookProof_HermiteLadder_exists_ladderOrd_hamPolyL
-- name    : BookProof.HermiteLadder.exists_ladderOrd_hamPolyL
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T14:45:52.835091+00:00
-- url     : https://prove2.me/theorems/2024d5c1-4ebe-450b-9d68-5e937d670c66
-- title:
--   `BookProof.HermiteLadder.exists_ladderOrd_hamPolyL` (S : Finset (Fin d)) (q : MvPolynomial (Fin d) ℂ) : ∃ n, LadderOrd (hamPolyL S q) n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteLadderOrder`.
--
--   `BookProof.HermiteLadder.exists_ladderOrd_hamPolyL` (S : Finset (Fin d)) (q : MvPolynomial (Fin d) ℂ) : ∃ n, LadderOrd (hamPolyL S q) n
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteLadder.exists_ladderOrd_hamPolyL`.

-- Generated from ChapterHermiteLadderOrder.lean — theorem BookProof.HermiteLadder.exists_ladderOrd_hamPolyL
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterDegSchrodingerCore
import Mathlib
import Definitions.Def_ChapterHermiteLadderOrder
import Definitions.Def_ChapterSirkFinitePrecision
import Definitions.Def_ChapterFockWeightedSchurEsa
import Definitions.Def_ChapterHermiteLadderShift
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval
open BookProof.HermiteLadder



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs BookProof.DegSchrodinger
open scoped ENNReal

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteLadder.exists_ladderOrd_hamPolyL (S : Finset (Fin d)) (q : MvPolynomial (Fin d) ℂ) :
    ∃ n, LadderOrd (hamPolyL S q) n := by sorry
