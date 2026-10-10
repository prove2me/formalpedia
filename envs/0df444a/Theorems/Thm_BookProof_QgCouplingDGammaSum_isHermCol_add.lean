-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_isHermCol_add
-- name    : BookProof.QgCouplingDGammaSum.isHermCol_add
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:19:32.06098+00:00
-- url     : https://prove2.me/theorems/50fe12fe-630d-4cbf-a032-c24f7c7e8d97
-- title:
--   `BookProof.QgCouplingDGammaSum.isHermCol_add` {a b : ℕ → (ℕ →₀ ℂ)} (ha : IsHermCol a) (hb : IsHermCol b) : IsHermCol (fun k => a k + b k)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.isHermCol_add` {a b : ℕ → (ℕ →₀ ℂ)} (ha : IsHermCol a) (hb : IsHermCol b) : IsHermCol (fun k => a k + b k)
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.isHermCol_add`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.isHermCol_add
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

theorem BookProof.QgCouplingDGammaSum.isHermCol_add {a b : ℕ → (ℕ →₀ ℂ)} (ha : IsHermCol a) (hb : IsHermCol b) :
    IsHermCol (fun k => a k + b k) := by sorry
