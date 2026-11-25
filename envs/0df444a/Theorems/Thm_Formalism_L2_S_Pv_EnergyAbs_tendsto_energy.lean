-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_tendsto_energy
-- name    : Formalism.L2.S.Pv.EnergyAbs.tendsto_energy
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:15:58.167441+00:00
-- url     : https://prove2.me/theorems/62aaae66-48c4-51ec-90de-cd03068263c7
-- title:
--   Energy Abs: tendsto energy
-- statement:
--   The Energy Abs construction uses the tendsto energy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsEnergy.lean#L50-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsEnergy.lean#L50-L71

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsSchur
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTrunc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsEnergy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem Formalism.L2.S.Pv.EnergyAbs.tendsto_energy {d : ℝ} (hd : 0 < d) {a b : ℕ → ℝ≥0∞} (ha : ∀ n, 0 < a n ∧ a n < ⊤)
    (hb : ∀ n, 0 < b n ∧ b n < ⊤) {N N' : ℕ → ℝ}
    (hN : Tendsto (fun n => N n / (a n).toReal) atTop (𝓝 (1 / d)))
    (hN' : Tendsto (fun n => N' n / (b n).toReal) atTop (𝓝 (1 / d))) :
    Tendsto (fun n => (a n * b n)⁻¹ * ENNReal.ofReal (d * N n * N' n)) atTop (𝓝 (ENNReal.ofReal (1 / d))) := by sorry
