-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_integral_liftedRankOneKernel
-- name    : Formalism.L2.S.Pv.EnergyAbs.integral_liftedRankOneKernel
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:16:39.482802+00:00
-- url     : https://prove2.me/theorems/37736112-077f-421a-b9e5-f8230f4df6f4
-- title:
--   Energy Abs: integral lifted Rank One Kernel
-- statement:
--   The Energy Abs construction uses the integral lifted Rank One Kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsTail.lean#L42-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsTail.lean#L42-L55

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTrunc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTail
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
variable {μ ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
  {σ : G → (HH →L[ℂ] HH)} {d : ℝ} {w : HH} {S S' : Set G} {τ : G → (V →L[ℂ] V)}
  {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}

theorem Formalism.L2.S.Pv.EnergyAbs.integral_liftedRankOneKernel [μ.IsMulLeftInvariant] [SFinite μ] (hσ : IsUnitRep σ) (hW : IsWAbs μ σ d w S τ ν W)
    (hW' : IsWAbs μ σ d w S' τ' ν' W') (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S')
    (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0)
    (hm : μ = (ν.prod μS).map φinv) (hm' : μ = (ν'.prod μS').map φinv) (γ : G)
    (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤) :
    ∫ q, K4 σ d w W W' γ q ∂((ν.prod μS).prod (ν'.prod μS')) = ∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ := by sorry
