-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_Fk_bound
-- name    : Formalism.L2.S.Pv.EnergyAbs.Fk_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:25:19.788038+00:00
-- url     : https://prove2.me/theorems/81df4ed4-8166-4346-83bf-bf1f6b250b75
-- title:
--   Energy Abs: Fk bound
-- statement:
--   The Energy Abs construction uses the Fk bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsFolnerExp.lean#L109-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsFolnerExp.lean#L109-L123

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerConv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem Formalism.L2.S.Pv.EnergyAbs.Fk_bound {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {w : HH} (hw : ‖w‖ = 1) {S : Set G}
    {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (z z' : G) {q : G} (hq : q ∈ S) : ‖Fk σ w W z z' q‖ ≤ ‖W z‖ * ‖W z'‖ := by sorry
