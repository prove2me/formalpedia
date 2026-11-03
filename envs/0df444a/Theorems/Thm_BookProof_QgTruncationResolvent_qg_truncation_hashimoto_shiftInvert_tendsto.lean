-- Prove2me | Theorems.Thm_BookProof_QgTruncationResolvent_qg_truncation_hashimoto_shiftInvert_tendsto
-- name    : BookProof.QgTruncationResolvent.qg_truncation_hashimoto_shiftInvert_tendsto
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-02T09:33:47.56455+00:00
-- url     : https://prove2.me/theorems/ef319309-3d9b-470c-b3ce-ce1a07c44949
-- title:
--   `BookProof.QgTruncationResolvent.qg_truncation_hashimoto_shiftInvert_tendsto` (Λ : ℕ → Set ι) (hexh : ∀ F : Finset ι, ∀ᶠ n in atTop, ∀ a ∈ F, a ∈ Λ n) : ∃ (T :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgTruncationResolvent`.
--
--   `BookProof.QgTruncationResolvent.qg_truncation_hashimoto_shiftInvert_tendsto` (Λ : ℕ → Set ι) (hexh : ∀ F : Finset ι, ∀ᶠ n in atTop, ∀ a ∈ F, a ∈ Λ n) : ∃ (T : UnboundedSelfAdjoint (Sec ι)) (S : ℕ → UnboundedSelfAdjoint (Sec ι)), IsSelfAdjointExtension (secHam W Q) T.op ∧ (∀ n, IsSelfAdjointExtension (secHam W (truncModes Q (Λ n))) (S n).op) ∧ IsShiftInvertC T.op Complex.I (-(T.resCLM 1)) ∧ (∀ n, IsShiftInvertC (S n).op Complex.I (-((S n).resCLM 1))) ∧ ∀ u : Sec ι, Tendsto (fun n => -((S n).resCLM 1 u)) atTop (𝓝 (-(T.resCLM 1 u)))
--
--   Formalization note: Lean 4 identifier `BookProof.QgTruncationResolvent.qg_truncation_hashimoto_shiftInvert_tendsto`.

-- Generated from ChapterQgTruncationResolvent.lean — theorem BookProof.QgTruncationResolvent.qg_truncation_hashimoto_shiftInvert_tendsto
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Mathlib
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterHashimotoComplexShifts
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterQgTimeIndependentFlow
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.EsaClosure
open BookProof.HashimotoShiftInvert
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent
open BookProof.QgTruncationResolvent



open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.QgOuterFockCoreFL BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.ScalaronEsa BookProof.DirectSumEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {ι : Type*}
variable (W : WallPot) (Q : QgModeData ι)

theorem BookProof.QgTruncationResolvent.qg_truncation_hashimoto_shiftInvert_tendsto (Λ : ℕ → Set ι)
    (hexh : ∀ F : Finset ι, ∀ᶠ n in atTop, ∀ a ∈ F, a ∈ Λ n) :
    ∃ (T : UnboundedSelfAdjoint (Sec ι)) (S : ℕ → UnboundedSelfAdjoint (Sec ι)),
      IsSelfAdjointExtension (secHam W Q) T.op ∧
        (∀ n, IsSelfAdjointExtension (secHam W (truncModes Q (Λ n))) (S n).op) ∧
        IsShiftInvertC T.op Complex.I (-(T.resCLM 1)) ∧
        (∀ n, IsShiftInvertC (S n).op Complex.I (-((S n).resCLM 1))) ∧
        ∀ u : Sec ι, Tendsto (fun n => -((S n).resCLM 1 u)) atTop (𝓝 (-(T.resCLM 1 u))) := by sorry
