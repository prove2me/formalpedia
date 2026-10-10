-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_comparison_friedrichs
-- name    : BookProof.QgCouplingDGammaSum.comparison_friedrichs
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:20:07.237601+00:00
-- url     : https://prove2.me/theorems/fb3bb4ab-126e-47f9-bdea-ffd29b54ee52
-- title:
--   `BookProof.QgCouplingDGammaSum.comparison_friedrichs` {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)} (hherm : ∀ i ∈ s, IsHermCol (cols i)) (hpos : ∀ i ∈ s, IsPosCol (cols i))...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.comparison_friedrichs` {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)} (hherm : ∀ i ∈ s, IsHermCol (cols i)) (hpos : ∀ i ∈ s, IsPosCol (cols i)) : ∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock), IsPositiveSelfAdjointExtension (dGammaOp (comparisonCol s cols)) A
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.comparison_friedrichs`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.comparison_friedrichs
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.YangMillsFriedrichs
open BookProof.QgCouplingDGammaSum



open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

theorem BookProof.QgCouplingDGammaSum.comparison_friedrichs {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)}
    (hherm : ∀ i ∈ s, IsHermCol (cols i)) (hpos : ∀ i ∈ s, IsPosCol (cols i)) :
    ∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock),
      IsPositiveSelfAdjointExtension (dGammaOp (comparisonCol s cols)) A := by sorry
