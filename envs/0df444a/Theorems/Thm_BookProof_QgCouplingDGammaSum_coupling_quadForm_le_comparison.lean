-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_coupling_quadForm_le_comparison
-- name    : BookProof.QgCouplingDGammaSum.coupling_quadForm_le_comparison
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:20:02.196814+00:00
-- url     : https://prove2.me/theorems/52b44b4c-ff40-405c-a2bc-543c9dacd7ca
-- title:
--   `BookProof.QgCouplingDGammaSum.coupling_quadForm_le_comparison` {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)} (hpos : ∀ i ∈ s, IsPosCol (cols i)) {i : ι} (hi : i ∈ s) (x :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.coupling_quadForm_le_comparison` {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)} (hpos : ∀ i ∈ s, IsPosCol (cols i)) {i : ι} (hi : i ∈ s) (x : lpFiniteModes Conf) : quadForm (dGammaOp (cols i)) x ≤ quadForm (dGammaOp (comparisonCol s cols)) x
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.coupling_quadForm_le_comparison`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.coupling_quadForm_le_comparison
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.QgCouplingDGammaSum



open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

theorem BookProof.QgCouplingDGammaSum.coupling_quadForm_le_comparison {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)}
    (hpos : ∀ i ∈ s, IsPosCol (cols i)) {i : ι} (hi : i ∈ s) (x : lpFiniteModes Conf) :
    quadForm (dGammaOp (cols i)) x ≤ quadForm (dGammaOp (comparisonCol s cols)) x := by sorry
