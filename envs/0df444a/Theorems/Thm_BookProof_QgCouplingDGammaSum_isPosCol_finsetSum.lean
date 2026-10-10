-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_isPosCol_finsetSum
-- name    : BookProof.QgCouplingDGammaSum.isPosCol_finsetSum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:17:34.319078+00:00
-- url     : https://prove2.me/theorems/a7b3b67e-7923-402b-8168-b096408a0e2e
-- title:
--   `BookProof.QgCouplingDGammaSum.isPosCol_finsetSum` {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)} (h : ∀ i ∈ s, IsPosCol (cols i)) : IsPosCol (fun k => ∑ i ∈ s, cols i k)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.isPosCol_finsetSum` {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)} (h : ∀ i ∈ s, IsPosCol (cols i)) : IsPosCol (fun k => ∑ i ∈ s, cols i k)
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.isPosCol_finsetSum`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.isPosCol_finsetSum
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

theorem BookProof.QgCouplingDGammaSum.isPosCol_finsetSum {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)}
    (h : ∀ i ∈ s, IsPosCol (cols i)) : IsPosCol (fun k => ∑ i ∈ s, cols i k) := by sorry
