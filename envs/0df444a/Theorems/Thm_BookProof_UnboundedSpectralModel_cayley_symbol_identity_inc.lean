-- Prove2me | Theorems.Thm_BookProof_UnboundedSpectralModel_cayley_symbol_identity_inc
-- name    : BookProof.UnboundedSpectralModel.cayley_symbol_identity_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T13:59:19.918032+00:00
-- url     : https://prove2.me/theorems/3d9a8db0-3599-4d12-8af1-0e8119504100
-- title:
--   `BookProof.UnboundedSpectralModel.cayley_symbol_identity_inc` (T : UnboundedSelfAdjoint H) : coordFn (resOp T) - star (coordFn (resOp T)) - (2 * Complex.I) • (star (coordFn (resOp T))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnboundedSpectralModel`.
--
--   `BookProof.UnboundedSpectralModel.cayley_symbol_identity_inc` (T : UnboundedSelfAdjoint H) : coordFn (resOp T) - star (coordFn (resOp T)) - (2 * Complex.I) • (star (coordFn (resOp T)) * coordFn (resOp T)) = (2 * Complex.I) • cayleyFn T
--
--   Formalization note: Lean 4 identifier `BookProof.UnboundedSpectralModel.cayley_symbol_identity_inc`.
--
--   Replaces the unuploadable node `BookProof_UnboundedSpectralModel_cayley_symbol_identity`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterUnboundedSpectralModel.lean — theorem BookProof.UnboundedSpectralModel.cayley_symbol_identity_inc
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterSpectralDirectSum
import Mathlib
import Definitions.Def_ChapterUnboundedSpectralModel
import Definitions.Def_ChapterStoneResolvent
open BookProof.UnboundedSpectralModel


noncomputable section

open MeasureTheory Complex
open scoped InnerProductSpace


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterSpectralDirectSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.UnboundedSpectralModel.cayley_symbol_identity_inc (T : UnboundedSelfAdjoint H) :
    coordFn (resOp T) - star (coordFn (resOp T))
        - (2 * Complex.I) • (star (coordFn (resOp T)) * coordFn (resOp T))
      = (2 * Complex.I) • cayleyFn T := by sorry
