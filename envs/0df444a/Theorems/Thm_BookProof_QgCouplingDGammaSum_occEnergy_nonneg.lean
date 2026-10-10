-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_occEnergy_nonneg
-- name    : BookProof.QgCouplingDGammaSum.occEnergy_nonneg
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:18:13.460208+00:00
-- url     : https://prove2.me/theorems/9b487e4a-1dda-4466-89fb-cd0532eb225a
-- title:
--   `BookProof.QgCouplingDGammaSum.occEnergy_nonneg` {lam : ℕ → ℝ} (hlam : ∀ k, 0 ≤ lam k) (α : Conf) : 0 ≤ occEnergy lam α
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.occEnergy_nonneg` {lam : ℕ → ℝ} (hlam : ∀ k, 0 ≤ lam k) (α : Conf) : 0 ≤ occEnergy lam α
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.occEnergy_nonneg`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.occEnergy_nonneg
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.QgCouplingDGammaSum



open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

theorem BookProof.QgCouplingDGammaSum.occEnergy_nonneg {lam : ℕ → ℝ} (hlam : ∀ k, 0 ≤ lam k) (α : Conf) :
    0 ≤ occEnergy lam α := by sorry
