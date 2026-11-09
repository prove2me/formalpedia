-- Prove2me | Theorems.Thm_BookProof_QymTimeIndependent_ymFock_weylGauge_timeIndependent
-- name    : BookProof.QymTimeIndependent.ymFock_weylGauge_timeIndependent
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T20:49:07.984114+00:00
-- url     : https://prove2.me/theorems/b59bdbae-3cd5-4000-bf58-d111ef28542b
-- title:
--   `BookProof.QymTimeIndependent.ymFock_weylGauge_timeIndependent` : (∀ x : finiteModeDomain (coreBasis e), quadForm (ymHamiltonian (coreRepBasis e) fabc) x = 1 / 2 * (∑ m, ‖((piOps (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQymTimeIndependentFlow`.
--
--   `BookProof.QymTimeIndependent.ymFock_weylGauge_timeIndependent` : (∀ x : finiteModeDomain (coreBasis e), quadForm (ymHamiltonian (coreRepBasis e) fabc) x = 1 / 2 * (∑ m, ‖((piOps (coreRepBasis e) m x : finiteModeDomain (coreBasis e)) : L2d 99)‖ ^ 2) + 1 / 2 * ∑ m, ‖((magOps (coreRepBasis e) fabc m x : finiteModeDomain (coreBasis e)) : L2d 99)‖ ^ 2) ∧ ∃ T : UnboundedSelfAdjoint Fock, IsSelfAdjointExtension (dGammaOp (ymFockCol e fabc)) T.op ∧ (∀ t s : ℝ, prop T t s = T.stoneU (t - s)) ∧ (∀ (t s : ℝ) (x : Fock), ‖prop T t s x‖ = ‖x‖) ∧ (∀ (t s r : ℝ) (x : Fock), prop T t s (prop T s r x) = prop T t r x) ∧ (∀ t s u : ℝ, prop T (t + u) (s + u) = prop T t s) ∧ (∀ y : ℝ → Fock, IsSchrodingerSolution T y → ∀ t s : ℝ, y t = prop T t s (y s))
--
--   Formalization note: Lean 4 identifier `BookProof.QymTimeIndependent.ymFock_weylGauge_timeIndependent`.

-- Generated from ChapterQymTimeIndependentFlow.lean — theorem BookProof.QymTimeIndependent.ymFock_weylGauge_timeIndependent
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterSirkSingleTimeShift
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Definitions.Def_ChapterFiniteSectionSingleTime
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterQymTimeIndependentFlow
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterQymTimeIndependentFlow
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterSirkBandLedger
open BookProof.EsaClosure
open BookProof.FockSecondQuantization
open BookProof.HermiteGalerkin
open BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs
open BookProof.YangMillsHermite
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

theorem BookProof.QymTimeIndependent.ymFock_weylGauge_timeIndependent :
    (∀ x : finiteModeDomain (coreBasis e),
        quadForm (ymHamiltonian (coreRepBasis e) fabc) x
          = 1 / 2 * (∑ m, ‖((piOps (coreRepBasis e) m x : finiteModeDomain (coreBasis e)) :
              L2d 99)‖ ^ 2)
            + 1 / 2 * ∑ m, ‖((magOps (coreRepBasis e) fabc m x :
                finiteModeDomain (coreBasis e)) : L2d 99)‖ ^ 2) ∧
      ∃ T : UnboundedSelfAdjoint Fock,
        IsSelfAdjointExtension (dGammaOp (ymFockCol e fabc)) T.op ∧
          (∀ t s : ℝ, prop T t s = T.stoneU (t - s)) ∧
          (∀ (t s : ℝ) (x : Fock), ‖prop T t s x‖ = ‖x‖) ∧
          (∀ (t s r : ℝ) (x : Fock), prop T t s (prop T s r x) = prop T t r x) ∧
          (∀ t s u : ℝ, prop T (t + u) (s + u) = prop T t s) ∧
          (∀ y : ℝ → Fock, IsSchrodingerSolution T y → ∀ t s : ℝ, y t = prop T t s (y s)) := by sorry
