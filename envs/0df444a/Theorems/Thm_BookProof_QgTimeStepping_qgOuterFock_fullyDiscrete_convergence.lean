-- Prove2me | Theorems.Thm_BookProof_QgTimeStepping_qgOuterFock_fullyDiscrete_convergence
-- name    : BookProof.QgTimeStepping.qgOuterFock_fullyDiscrete_convergence
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:35:39.187758+00:00
-- url     : https://prove2.me/theorems/fb67f179-ba65-4f95-a3a4-7eb032c0d1c6
-- title:
--   `BookProof.QgTimeStepping.qgOuterFock_fullyDiscrete_convergence` (W : WallPot) (Q : QgModeData ι) (Λ : ℕ → Set ι) (hexh : ∀ F : Finset ι, ∀ᶠ n in atTop, ∀ a ∈ F, a ∈ Λ n) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgTimeStepping`.
--
--   `BookProof.QgTimeStepping.qgOuterFock_fullyDiscrete_convergence` (W : WallPot) (Q : QgModeData ι) (Λ : ℕ → Set ι) (hexh : ∀ F : Finset ι, ∀ᶠ n in atTop, ∀ a ∈ F, a ∈ Λ n) : ∃ (T : UnboundedSelfAdjoint (Sec ι)) (S : ℕ → UnboundedSelfAdjoint (Sec ι)), IsSelfAdjointExtension (secHam W Q) T.op ∧ (∀ n, IsSelfAdjointExtension (secHam W (truncModes Q (Λ n))) (S n).op) ∧ ∀ (v : Sec ι) (t : ℝ), 0 < t → ∃ k : ℕ → ℕ, (∀ n, 0 < k n) ∧ Tendsto (fun n => (cnStep (S n) (t / (k n)))^[k n] v) atTop (𝓝 (T.stoneU t v))
--
--   Formalization note: Lean 4 identifier `BookProof.QgTimeStepping.qgOuterFock_fullyDiscrete_convergence`.

-- Generated from ChapterQgTimeStepping.lean — theorem BookProof.QgTimeStepping.qgOuterFock_fullyDiscrete_convergence
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgTruncationResolvent
import Mathlib
import Definitions.Def_ChapterQgTimeStepping
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterQgTimeIndependentFlow
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.EsaClosure
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent
open BookProof.QgTimeStepping



open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgOuterFockCoreFL BookProof.QgTruncationResolvent

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)
variable {ι : Type*}

theorem BookProof.QgTimeStepping.qgOuterFock_fullyDiscrete_convergence (W : WallPot) (Q : QgModeData ι) (Λ : ℕ → Set ι)
    (hexh : ∀ F : Finset ι, ∀ᶠ n in atTop, ∀ a ∈ F, a ∈ Λ n) :
    ∃ (T : UnboundedSelfAdjoint (Sec ι)) (S : ℕ → UnboundedSelfAdjoint (Sec ι)),
      IsSelfAdjointExtension (secHam W Q) T.op ∧
        (∀ n, IsSelfAdjointExtension (secHam W (truncModes Q (Λ n))) (S n).op) ∧
        ∀ (v : Sec ι) (t : ℝ), 0 < t →
          ∃ k : ℕ → ℕ, (∀ n, 0 < k n) ∧
            Tendsto (fun n => (cnStep (S n) (t / (k n)))^[k n] v) atTop
              (𝓝 (T.stoneU t v)) := by sorry
