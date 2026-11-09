-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_dGammaOp_commForm_bound_w
-- name    : BookProof.FockWeightedSchur.dGammaOp_commForm_bound_w
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T09:28:05.42804+00:00
-- url     : https://prove2.me/theorems/bbaf0bec-dc10-4c89-abeb-26b9f88ef795
-- title:
--   `BookProof.FockWeightedSchur.dGammaOp_commForm_bound_w` (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col) (hBg : WCommBound w col B) (x : lpFiniteModes Conf) : |(-2 : ℝ) * (inner ℂ (dGam
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.dGammaOp_commForm_bound_w` (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col) (hBg : WCommBound w col B) (x : lpFiniteModes Conf) : |(-2 : ℝ) * (inner ℂ (dGammaOp col x) ((diagMax (wSym w) (inclC (wSym w) x) : Fock)) : ℂ).im| ≤ B * (inner ℂ ((x : Fock)) ((diagMax (wSym w) (inclC (wSym w) x) : Fock)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.dGammaOp_commForm_bound_w`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.dGammaOp_commForm_bound_w
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Definitions.Def_ChapterSirkBandLedger
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow.IkebeKato
open BookProof.FockWeightedSchur



open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {w : ℕ → ℝ}
variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}

theorem BookProof.FockWeightedSchur.dGammaOp_commForm_bound_w (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col)
    (hBg : WCommBound w col B) (x : lpFiniteModes Conf) :
    |(-2 : ℝ) * (inner ℂ (dGammaOp col x)
        ((diagMax (wSym w) (inclC (wSym w) x) : Fock)) : ℂ).im|
      ≤ B * (inner ℂ ((x : Fock)) ((diagMax (wSym w) (inclC (wSym w) x) : Fock)) : ℂ).re := by sorry
