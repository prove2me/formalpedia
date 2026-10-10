-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_isHermCol_finsetSum
-- name    : BookProof.QgCouplingDGammaSum.isHermCol_finsetSum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:17:30.995975+00:00
-- url     : https://prove2.me/theorems/879873e8-2b1f-4802-979f-cac1131ebd0c
-- title:
--   `BookProof.QgCouplingDGammaSum.isHermCol_finsetSum` {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)} (h : ∀ i ∈ s, IsHermCol (cols i)) : IsHermCol (fun k => ∑ i ∈ s, cols i k)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.isHermCol_finsetSum` {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)} (h : ∀ i ∈ s, IsHermCol (cols i)) : IsHermCol (fun k => ∑ i ∈ s, cols i k)
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.isHermCol_finsetSum`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.isHermCol_finsetSum
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

theorem BookProof.QgCouplingDGammaSum.isHermCol_finsetSum {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)}
    (h : ∀ i ∈ s, IsHermCol (cols i)) : IsHermCol (fun k => ∑ i ∈ s, cols i k) := by sorry
