-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_ConvG_triple_lintegral_eq
-- name    : Formalism.L2.S.Pv.ConvG.triple_lintegral_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:46:28.329418+00:00
-- url     : https://prove2.me/theorems/01c74f13-1ad4-5975-9093-c9767df87053
-- title:
--   Conv G: triple lintegral eq
-- statement:
--   The Conv G construction uses the triple lintegral eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/ConvGGG.lean#L97-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/ConvGGG.lean#L97-L127

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
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
  {V V' : Type} [NormedAddCommGroup V] [NormedAddCommGroup V']

theorem Formalism.L2.S.Pv.ConvG.triple_lintegral_eq {μ μS ν : Measure G} [SFinite μS] [SFinite ν] {S : Set G} {σ : G → (HH →L[ℂ] HH)}
    (hσ : IsUnitRep σ) (w : HH) {W : G → V} (hWc : Continuous W)
    (hWe : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS ∂ν)
    (h0 : μS Sᶜ = 0) (hWS : ∀ s ∈ S, ∀ x, ‖W (s * x)‖ = ‖W x‖) :
    ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν =
      ∫⁻ z, ‖W z‖ₑ * ∫⁻ y, ‖⟪σ z w, σ y w⟫_ℂ‖ₑ * ‖W y‖ₑ ∂μ ∂ν := by sorry
