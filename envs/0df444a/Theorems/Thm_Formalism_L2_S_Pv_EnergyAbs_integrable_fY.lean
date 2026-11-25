-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_integrable_fY
-- name    : Formalism.L2.S.Pv.EnergyAbs.integrable_fY
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:21:28.88404+00:00
-- url     : https://prove2.me/theorems/8c832ec3-024c-4bf9-a6bd-5fc0bb5bacfa
-- title:
--   Energy Abs: integrable f Y
-- statement:
--   The Energy Abs construction uses the integrable f Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsTrunc.lean#L56-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsTrunc.lean#L56-L71

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsSchur
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTrunc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem Formalism.L2.S.Pv.EnergyAbs.integrable_fY {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν : Measure G} [SFinite ν]
    [SFinite μS] {d : ℝ} {w : HH} {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) (hinv : ∀ a ∈ S, a⁻¹ ∈ S) {A : Set G} (hA : MeasurableSet A) (hAS : A ⊆ S)
    (hAf : μS A < ⊤) (e : V) : Integrable (fY σ w W e) (ν.prod (μS.restrict A)) := by sorry
