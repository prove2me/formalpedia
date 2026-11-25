-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_folner_limit
-- name    : Formalism.L2.S.Pv.EnergyAbs.folner_limit
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:15:48.915226+00:00
-- url     : https://prove2.me/theorems/d9f5afe7-5790-5c35-b5e4-49d95854b595
-- title:
--   Energy Abs: folner limit
-- statement:
--   The Energy Abs construction uses the folner limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsFolner.lean#L113-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsFolner.lean#L113-L167

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerConv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerSum
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerLim
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolner
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
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem Formalism.L2.S.Pv.EnergyAbs.folner_limit {μ : Measure G} [μ.IsHaarMeasure] {σ : G → (HH →L[ℂ] HH)} {d : ℝ} {w : HH}
    {S : Set G} {μS ν : Measure G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hσ : IsUnitRep σ) (hSch : IsSchur μ σ d) (hw : ‖w‖ = 1) (hS : IsHaarSub S μS) (hν : SFinite ν)
    (hq : IsQuot μ μS ν) (hW : IsWAbs μ σ d w S τ ν W)
    (hconv : ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν < ⊤)
    (Ω : ℕ → Set G) (hΩ : ∀ n, MeasurableSet (Ω n) ∧ Ω n ⊆ S ∧ 0 < μS (Ω n) ∧ μS (Ω n) < ⊤)
    (hF : ∀ K : Set G, IsCompact K → K ⊆ S →
      Tendsto (fun n => (μS {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n}).toReal / (μS (Ω n)).toReal) atTop (𝓝 1)) :
    Tendsto (fun n => (∑ i, ‖yv μS ν σ w W (Ω n) (stdOrthonormalBasis ℂ V i)‖ ^ 2) / (μS (Ω n)).toReal)
      atTop (𝓝 (1 / d)) := by sorry
