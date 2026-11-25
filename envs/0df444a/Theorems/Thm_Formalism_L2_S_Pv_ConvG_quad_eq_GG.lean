-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_ConvG_quad_eq_GG
-- name    : Formalism.L2.S.Pv.ConvG.quad_eq_GG
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:25:32.493375+00:00
-- url     : https://prove2.me/theorems/df2bb32d-81ef-430f-b23f-1870a83adada
-- title:
--   Conv G: quad eq GG
-- statement:
--   The Conv G construction uses the quad eq GG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/ConvGGG.lean#L42-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/ConvGGG.lean#L42-L95

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

theorem Formalism.L2.S.Pv.ConvG.quad_eq_GG {μ μS ν μS' ν' : Measure G} [SFinite μS] [SFinite ν] [SFinite μS'] [SFinite ν'] [SFinite μ]
    {S S' : Set G} {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} {W' : G → V'}
    (hWc : Continuous W) (hWc' : Continuous W')
    (hWe : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS ∂ν)
    (hWe' : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS' ∂ν')
    (hinv : μS.map (fun x => x⁻¹) = μS) (hinv' : μS'.map (fun x => x⁻¹) = μS')
    (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0) (hiS : ∀ a ∈ S, a⁻¹ ∈ S) (hiS' : ∀ a ∈ S', a⁻¹ ∈ S')
    (hWS : ∀ s ∈ S, ∀ x, ‖W (s * x)‖ = ‖W x‖) (hWS' : ∀ s ∈ S', ∀ x, ‖W' (s * x)‖ = ‖W' x‖) (γ : G) :
    ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪σ z w, σ (s * γ * s'⁻¹) (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W' z'‖ₑ ∂μS' ∂μS ∂ν' ∂ν =
      ∫⁻ x, ∫⁻ y, PhiGG σ w W W' γ x y ∂μ ∂μ := by sorry
