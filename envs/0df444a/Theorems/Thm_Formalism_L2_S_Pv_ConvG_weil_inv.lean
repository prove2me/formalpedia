-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_ConvG_weil_inv
-- name    : Formalism.L2.S.Pv.ConvG.weil_inv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:25:16.120016+00:00
-- url     : https://prove2.me/theorems/8cd6605b-f8c8-4632-9900-4d1d4d7c333a
-- title:
--   Conv G: weil inv
-- statement:
--   The Conv G construction uses the weil inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/ConvGGG.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/ConvGGG.lean#L16-L24

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_ConvGGG
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
open scoped InnerProductSpace ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.ConvG
open Formalism.L2.SG.Pf.EnergyAbs Formalism.L2.S.Pv.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

theorem Formalism.L2.S.Pv.ConvG.weil_inv {μ μS ν : Measure G} [SFinite μS] [SFinite ν]
    (hW : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS ∂ν)
    (hinv : μS.map (fun x => x⁻¹) = μS) (Ψ : G → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ z, ∫⁻ s, Ψ (s⁻¹ * z) ∂μS ∂ν = ∫⁻ x, Ψ x ∂μ := by sorry
