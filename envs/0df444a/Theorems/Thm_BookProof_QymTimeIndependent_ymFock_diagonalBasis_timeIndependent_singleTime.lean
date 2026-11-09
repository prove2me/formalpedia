-- Prove2me | Theorems.Thm_BookProof_QymTimeIndependent_ymFock_diagonalBasis_timeIndependent_singleTime
-- name    : BookProof.QymTimeIndependent.ymFock_diagonalBasis_timeIndependent_singleTime
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T20:45:49.954109+00:00
-- url     : https://prove2.me/theorems/42c6f89a-3f76-40e4-acf6-829fd08f4ce6
-- title:
--   `BookProof.QymTimeIndependent.ymFock_diagonalBasis_timeIndependent_singleTime` (en : ℕ ≃ Conf) (lam : ℕ → ℝ) (hlam : ∀ k, 0 ≤ lam k) (hdiag : ymFockCol e fabc = diagCol lam) : ∃ (T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQymTimeIndependentFlow`.
--
--   `BookProof.QymTimeIndependent.ymFock_diagonalBasis_timeIndependent_singleTime` (en : ℕ ≃ Conf) (lam : ℕ → ℝ) (hlam : ∀ k, 0 ≤ lam k) (hdiag : ymFockCol e fabc = diagCol lam) : ∃ (T : UnboundedSelfAdjoint Fock) (S : ℕ → UnboundedSelfAdjoint Fock), IsSelfAdjointExtension (dGammaOp (ymFockCol e fabc)) T.op ∧ (∀ n, IsSelfAdjointExtension (((secOp (dGammaOp (ymFockCol e fabc)) (windowOfEquiv en n) : Fock →ₗ[ℂ] Fock)).comp (lpFiniteModes Conf).subtype) (S n).op) ∧ (∀ t s : ℝ, prop T t s = T.stoneU (t - s)) ∧ (∀ (t s : ℝ) (x : Fock), ‖prop T t s x‖ = ‖x‖) ∧ (∀ (t s r : ℝ) (x : Fock), prop T t s (prop T s r x) = prop T t r x) ∧ (∀ t s u : ℝ, prop T (t + u) (s + u) = prop T t s) ∧ (∀ y : ℝ → Fock, IsSchrodingerSolution T y → ∀ t s : ℝ, y t = prop T t s (y s)) ∧ (∀ l : ℝ, l ≠ 0 → IsShiftInvertC T.op (((l : ℝ) : ℂ) * Complex.I) (-(T.resCLM l)) ∧ (∀ n, IsShiftInvertC (S n).op (((l : ℝ) : ℂ) * Complex.I) (-((S n).resCLM l))) ∧ ∀ u : Fock, Tendsto (fun n => -((S n).resCLM l u)) atTop (𝓝 (-(T.resCLM l u)))) ∧ ∀ (v : Fock) (t : ℝ), Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v))
--
--   Formalization note: Lean 4 identifier `BookProof.QymTimeIndependent.ymFock_diagonalBasis_timeIndependent_singleTime`.

-- Generated from ChapterQymTimeIndependentFlow.lean — theorem BookProof.QymTimeIndependent.ymFock_diagonalBasis_timeIndependent_singleTime
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterSirkSingleTimeShift
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Definitions.Def_ChapterFiniteSectionSingleTime
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterQymTimeIndependentFlow
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHashimotoComplexShifts
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterQymTimeIndependentFlow
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterSirkBandLedger
open BookProof.EsaClosure
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.HashimotoShiftInvert
open BookProof.NavierStokesFlow.IkebeKato
open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.HashimotoShiftInvert BookProof.SirkSingleTime BookProof.QgTimeIndependent
open BookProof.FiniteSectionSingleTime BookProof.YangMillsFriedrichs
open BookProof.FockSecondQuantization BookProof.QgCouplingDGammaSum
open BookProof.YangMillsHermite BookProof.HermiteGalerkin BookProof.HermiteProductCore
open BookProof.NavierStokesFlow

noncomputable section

variable (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)

theorem BookProof.QymTimeIndependent.ymFock_diagonalBasis_timeIndependent_singleTime (en : ℕ ≃ Conf) (lam : ℕ → ℝ)
    (hlam : ∀ k, 0 ≤ lam k) (hdiag : ymFockCol e fabc = BookProof.QgCouplingDGammaSum.diagCol lam) :
    ∃ (T : UnboundedSelfAdjoint Fock) (S : ℕ → UnboundedSelfAdjoint Fock),
      IsSelfAdjointExtension (dGammaOp (ymFockCol e fabc)) T.op ∧
        (∀ n, IsSelfAdjointExtension
          (((secOp (dGammaOp (ymFockCol e fabc)) (windowOfEquiv en n) :
              Fock →ₗ[ℂ] Fock)).comp (lpFiniteModes Conf).subtype) (S n).op) ∧
        (∀ t s : ℝ, prop T t s = T.stoneU (t - s)) ∧
        (∀ (t s : ℝ) (x : Fock), ‖prop T t s x‖ = ‖x‖) ∧
        (∀ (t s r : ℝ) (x : Fock), prop T t s (prop T s r x) = prop T t r x) ∧
        (∀ t s u : ℝ, prop T (t + u) (s + u) = prop T t s) ∧
        (∀ y : ℝ → Fock, IsSchrodingerSolution T y → ∀ t s : ℝ, y t = prop T t s (y s)) ∧
        (∀ l : ℝ, l ≠ 0 →
          IsShiftInvertC T.op (((l : ℝ) : ℂ) * Complex.I) (-(T.resCLM l)) ∧
            (∀ n, IsShiftInvertC (S n).op (((l : ℝ) : ℂ) * Complex.I) (-((S n).resCLM l))) ∧
            ∀ u : Fock, Tendsto (fun n => -((S n).resCLM l u)) atTop (𝓝 (-(T.resCLM l u)))) ∧
        ∀ (v : Fock) (t : ℝ), Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v)) := by sorry
