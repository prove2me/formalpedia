-- Prove2me | Theorems.Thm_BookProof_FockNumberPreservingGap_fock_gap_of_number_preserving_op
-- name    : BookProof.FockNumberPreservingGap.fock_gap_of_number_preserving_op
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:40:45.408409+00:00
-- url     : https://prove2.me/theorems/c8ca803f-5f4b-4448-83ff-482f602a9d4a
-- title:
--   `BookProof.FockNumberPreservingGap.fock_gap_of_number_preserving_op` {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hmu : 0 ≤ mu) (hgap : IsPosCol (shiftCol col mu)) : dGammaOp col (fockEquiv vac)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockNumberPreservingGap`.
--
--   `BookProof.FockNumberPreservingGap.fock_gap_of_number_preserving_op` {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hmu : 0 ≤ mu) (hgap : IsPosCol (shiftCol col mu)) : dGammaOp col (fockEquiv vac) = 0 ∧ ∀ x : lpFiniteModes Conf, (inner ℂ (toLp vac) ((x : Fock)) : ℂ) = 0 → mu * ‖(x : Fock)‖ ^ 2 ≤ quadForm (dGammaOp col) x
--
--   Formalization note: Lean 4 identifier `BookProof.FockNumberPreservingGap.fock_gap_of_number_preserving_op`.

-- Generated from ChapterFockNumberPreservingGap.lean — theorem BookProof.FockNumberPreservingGap.fock_gap_of_number_preserving_op
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.FockNumberPreservingGap


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

theorem BookProof.FockNumberPreservingGap.fock_gap_of_number_preserving_op {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hmu : 0 ≤ mu)
    (hgap : IsPosCol (shiftCol col mu)) :
    dGammaOp col (fockEquiv vac) = 0 ∧
      ∀ x : lpFiniteModes Conf, (inner ℂ (toLp vac) ((x : Fock)) : ℂ) = 0 →
        mu * ‖(x : Fock)‖ ^ 2 ≤ quadForm (dGammaOp col) x := by sorry
