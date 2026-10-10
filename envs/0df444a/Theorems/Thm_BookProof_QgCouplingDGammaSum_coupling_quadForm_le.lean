-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_coupling_quadForm_le
-- name    : BookProof.QgCouplingDGammaSum.coupling_quadForm_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:18:00.446975+00:00
-- url     : https://prove2.me/theorems/f91fcd61-507d-4a74-bf13-f07379d6ef44
-- title:
--   `BookProof.QgCouplingDGammaSum.coupling_quadForm_le` {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)} (hpos : ∀ i ∈ s, IsPosCol (cols i)) {i : ι} (hi : i ∈ s) (x : lpFiniteModes...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.coupling_quadForm_le` {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)} (hpos : ∀ i ∈ s, IsPosCol (cols i)) {i : ι} (hi : i ∈ s) (x : lpFiniteModes Conf) : quadForm (dGammaOp (cols i)) x ≤ quadForm (dGammaOp (fun k => ∑ j ∈ s, cols j k)) x
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.coupling_quadForm_le`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.coupling_quadForm_le
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.FockSecondQuantization
open BookProof.QgCouplingDGammaSum



open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

theorem BookProof.QgCouplingDGammaSum.coupling_quadForm_le {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)}
    (hpos : ∀ i ∈ s, IsPosCol (cols i)) {i : ι} (hi : i ∈ s) (x : lpFiniteModes Conf) :
    quadForm (dGammaOp (cols i)) x
      ≤ quadForm (dGammaOp (fun k => ∑ j ∈ s, cols j k)) x := by sorry
