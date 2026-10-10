-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_coupling_sum_friedrichs
-- name    : BookProof.QgCouplingDGammaSum.coupling_sum_friedrichs
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:20:37.548065+00:00
-- url     : https://prove2.me/theorems/e5732e38-1970-4bdb-8dd1-9100c9341354
-- title:
--   `BookProof.QgCouplingDGammaSum.coupling_sum_friedrichs` {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)} (hherm : ∀ i ∈ s, IsHermCol (cols i)) (hpos : ∀ i ∈ s, IsPosCol (cols i))...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.coupling_sum_friedrichs` {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)} (hherm : ∀ i ∈ s, IsHermCol (cols i)) (hpos : ∀ i ∈ s, IsPosCol (cols i)) : ∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock), IsPositiveSelfAdjointExtension (∑ i ∈ s, dGammaOp (cols i)) A
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.coupling_sum_friedrichs`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.coupling_sum_friedrichs
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.FockSecondQuantization
open BookProof.YangMillsFriedrichs
open BookProof.QgCouplingDGammaSum



open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

theorem BookProof.QgCouplingDGammaSum.coupling_sum_friedrichs {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)}
    (hherm : ∀ i ∈ s, IsHermCol (cols i)) (hpos : ∀ i ∈ s, IsPosCol (cols i)) :
    ∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock),
      IsPositiveSelfAdjointExtension (∑ i ∈ s, dGammaOp (cols i)) A := by sorry
