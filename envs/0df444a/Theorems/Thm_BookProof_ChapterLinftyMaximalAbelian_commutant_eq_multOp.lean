-- Prove2me | Theorems.Thm_BookProof_ChapterLinftyMaximalAbelian_commutant_eq_multOp
-- name    : BookProof.ChapterLinftyMaximalAbelian.commutant_eq_multOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T16:45:14.881991+00:00
-- url     : https://prove2.me/theorems/abf6d7f6-fd56-4d80-8f29-35cceeb3897b
-- title:
--   `BookProof.ChapterLinftyMaximalAbelian.commutant_eq_multOp` {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} (hT : CommutesWithMultOps T) : T = multOp (symbol T) (memLp_top_symbol hT)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLinftyMaximalAbelian`.
--
--   `BookProof.ChapterLinftyMaximalAbelian.commutant_eq_multOp` {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} (hT : CommutesWithMultOps T) : T = multOp (symbol T) (memLp_top_symbol hT)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLinftyMaximalAbelian.commutant_eq_multOp`.

-- Generated from ChapterLinftyMaximalAbelian.lean — theorem BookProof.ChapterLinftyMaximalAbelian.commutant_eq_multOp
import Mathlib
import Definitions.Def_ChapterLinftyMaximalAbelian
import Definitions.Def_ChapterLinftyMultiplication
import Theorems.Thm_BookProof_ChapterLinftyMaximalAbelian_memLp_top_symbol
open BookProof.ChapterLinftyMultiplication
open BookProof.ChapterLinftyMaximalAbelian


noncomputable section

open MeasureTheory ENNReal Complex


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

theorem BookProof.ChapterLinftyMaximalAbelian.commutant_eq_multOp {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} (hT : CommutesWithMultOps T) :
    T = multOp (symbol T) (memLp_top_symbol hT) := by sorry
