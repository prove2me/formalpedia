-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_point_lower
-- name    : Formalism.L2.S.Pv.EnergyAbs.point_lower
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:15:40.624129+00:00
-- url     : https://prove2.me/theorems/d91d0cd1-c39c-5186-af38-74b068443b4a
-- title:
--   Energy Abs: point lower
-- statement:
--   The Energy Abs construction uses the point lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsPoint.lean#L65-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsPoint.lean#L65-L123

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTrunc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTail
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsLower
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsEquiv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsPoint
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
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem Formalism.L2.S.Pv.EnergyAbs.point_lower {μ : Measure G} [μ.IsHaarMeasure] {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {d : ℝ}
    {w : HH} {S S' : Set G} {μS μS' ν ν' : Measure G} {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')}
    {W : G → V} {W' : G → V'} [SFinite ν] [SFinite ν'] (hS : IsHaarSub S μS) (hS' : IsHaarSub S' μS')
    (hq : IsQuot μ μS ν) (hq' : IsQuot μ μS' ν')
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    (Ω Ω' : ℕ → Set G) (hΩ : ∀ n, MeasurableSet (Ω n) ∧ Ω n ⊆ S ∧ 0 < μS (Ω n) ∧ μS (Ω n) < ⊤)
    (hΩ' : ∀ n, MeasurableSet (Ω' n) ∧ Ω' n ⊆ S' ∧ 0 < μS' (Ω' n) ∧ μS' (Ω' n) < ⊤)
    (hF : ∀ K : Set G, IsCompact K → K ⊆ S → Tendsto (fun n =>
      (μS {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n}).toReal / (μS (Ω n)).toReal) atTop (𝓝 1))
    (hF' : ∀ K : Set G, IsCompact K → K ⊆ S' → Tendsto (fun n =>
      (μS' {t | t ∈ Ω' n ∧ ∀ k ∈ K, k * t ∈ Ω' n}).toReal / (μS' (Ω' n)).toReal) atTop (𝓝 1))
    (hXc : ∀ n, Continuous (fun g => hsA (Xop μS ν μS' ν' σ d w W W' (Ω n) (Ω' n) g)))
    (γ : G) (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤) :
    ENNReal.ofReal (hsA (∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ)) ≤
      liminf (fun n => (μS (Ω n) * μS' (Ω' n))⁻¹ *
        ∫⁻ s, ∫⁻ s', ENNReal.ofReal (hsA (Xop μS ν μS' ν' σ d w W W' (Ω n) (Ω' n) (s * γ * s'⁻¹)))
          ∂μS' ∂μS) atTop := by sorry
