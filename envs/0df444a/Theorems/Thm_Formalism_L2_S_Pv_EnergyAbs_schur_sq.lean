-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_schur_sq
-- name    : Formalism.L2.S.Pv.EnergyAbs.schur_sq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:24:37.085433+00:00
-- url     : https://prove2.me/theorems/840d47bd-c5ff-48d7-85bc-0145f460341e
-- title:
--   Energy Abs: schur sq
-- statement:
--   The Energy Abs construction uses the schur sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsSchur.lean#L44-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsSchur.lean#L44-L65

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsSchur
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem Formalism.L2.S.Pv.EnergyAbs.schur_sq {μ : Measure G} {σ : G → (HH →L[ℂ] HH)} {d : ℝ} (hS : IsSchur μ σ d) (a b : HH) :
    Integrable (fun γ => ‖⟪a, σ γ b⟫_ℂ‖ ^ 2) μ ∧
      ∫ γ, ‖⟪a, σ γ b⟫_ℂ‖ ^ 2 ∂μ = ‖a‖ ^ 2 * ‖b‖ ^ 2 / d := by sorry
