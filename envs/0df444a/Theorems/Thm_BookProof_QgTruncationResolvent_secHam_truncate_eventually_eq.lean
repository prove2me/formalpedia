-- Prove2me | Theorems.Thm_BookProof_QgTruncationResolvent_secHam_truncate_eventually_eq
-- name    : BookProof.QgTruncationResolvent.secHam_truncate_eventually_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-05T13:11:31.237459+00:00
-- url     : https://prove2.me/theorems/ba02fbdf-b1b4-4adc-85b3-88190f2e5d1a
-- title:
--   `BookProof.QgTruncationResolvent.secHam_truncate_eventually_eq` (Λ : ℕ → Set ι) (hexh : ∀ F : Finset ι, ∀ᶠ n in atTop, ∀ a ∈ F, a ∈ Λ n) (x : secCore (ι
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgTruncationResolvent`.
--
--   `BookProof.QgTruncationResolvent.secHam_truncate_eventually_eq` (Λ : ℕ → Set ι) (hexh : ∀ F : Finset ι, ∀ᶠ n in atTop, ∀ a ∈ F, a ∈ Λ n) (x : secCore (ι
--
--   Formalization note: Lean 4 identifier `BookProof.QgTruncationResolvent.secHam_truncate_eventually_eq`.

-- Generated from ChapterQgTruncationResolvent.lean — theorem BookProof.QgTruncationResolvent.secHam_truncate_eventually_eq
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Mathlib
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterScalaronFiberFL
open BookProof.ScalaronFiberFL
open BookProof.ScalaronFiberFL.WallPot
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

theorem BookProof.QgTruncationResolvent.secHam_truncate_eventually_eq (Λ : ℕ → Set ι)
    (hexh : ∀ F : Finset ι, ∀ᶠ n in atTop, ∀ a ∈ F, a ∈ Λ n) (x : secCore (ι := ι)) :
    ∀ᶠ n in atTop, secHam W (truncModes Q (Λ n)) x = secHam W Q x := by sorry
