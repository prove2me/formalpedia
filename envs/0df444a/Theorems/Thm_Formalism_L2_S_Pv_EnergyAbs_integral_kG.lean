-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_integral_kG
-- name    : Formalism.L2.S.Pv.EnergyAbs.integral_kG
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:24:51.054127+00:00
-- url     : https://prove2.me/theorems/2bab9363-6f93-48ad-991f-bd25fb1d4ac8
-- title:
--   Energy Abs: integral k G
-- statement:
--   The Energy Abs construction uses the integral k G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsRep.lean#L46-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsRep.lean#L46-L79

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
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

theorem Formalism.L2.S.Pv.EnergyAbs.integral_kG {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ] {σ : G → (HH →L[ℂ] HH)}
    (hσ : IsUnitRep σ) {d : ℝ} {w : HH} {S : Set G} {τ : G → (V →L[ℂ] V)} {ν : Measure G} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) (W' : G → V') (γ : G) (hi : Integrable (kG σ d w W W' γ) (μ.prod μ)) :
    ∫ q, kG σ d w W W' γ q ∂(μ.prod μ) = ∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ := by sorry
