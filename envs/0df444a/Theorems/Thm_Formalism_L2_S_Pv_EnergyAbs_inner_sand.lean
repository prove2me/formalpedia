-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_inner_sand
-- name    : Formalism.L2.S.Pv.EnergyAbs.inner_sand
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:07:56.610909+00:00
-- url     : https://prove2.me/theorems/55acdc85-e2fb-4ad5-8357-26d2fe818ef5
-- title:
--   Energy Abs: inner sand
-- statement:
--   The Energy Abs construction uses the inner sand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsSchur.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsSchur.lean#L21-L23

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

theorem Formalism.L2.S.Pv.EnergyAbs.inner_sand (σ : G → (HH →L[ℂ] HH)) (Y : V →L[ℂ] HH) (Y' : V' →L[ℂ] HH) (γ : G) (a : V) (b : V') :
    ⟪a, sand σ Y Y' γ b⟫_ℂ = ⟪Y a, σ γ (Y' b)⟫_ℂ := by sorry
