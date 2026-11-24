-- Prove2me | Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_shift_general
-- name    : Formalism.L2.SG.MeasureShiftInvariance.shift_general
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:03.762421+00:00
-- url     : https://prove2.me/theorems/1abe34fa-8b86-4a63-90ba-04c859e91403
-- title:
--   Measure Shift Invariance: shift general
-- statement:
--   The Measure Shift Invariance construction uses the shift general property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CountableConjSub.lean#L325-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CountableConjSub.lean#L325-L407

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CountableConjSub
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
open scoped ENNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.MeasureShiftInvariance
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

theorem Formalism.L2.SG.MeasureShiftInvariance.shift_general (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (R Γ : Subgroup G) [Countable Γ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : G → E) (Ω : Set G) (h : G) (ν : Measure G)
    (hΓR : Γ ≤ R) (hK : ∃ K : Set G, IsCompact K ∧ ∀ r ∈ R, ∃ s ∈ Γ, s * r ∈ K)
    (hn : ∀ r, r ∈ R ↔ h⁻¹ * r * h ∈ R) (hσ : SigmaFinite ν) (hne : ν ≠ 0) (hcon : ν (R : Set G)ᶜ = 0)
    (hfin : ∀ K : Set G, IsCompact K → ν K < ⊤) (hleft : ∀ r ∈ R, ν.map (fun x => r * x) = ν)
    (hinvν : ν.map (fun x => x⁻¹) = ν) (hconj : ν.map (fun x => h⁻¹ * x * h) = ν)
    (hf : ∀ r ∈ R, ∀ x, f (r * x) = f x) (hΩ : SF (Γ : Set G) Ω) (hfi : IntegrableOn f Ω μ) :
    ∫ x in Ω, f x ∂μ = ∫ x in (fun x => h⁻¹ * x) '' Ω, f x ∂μ := by sorry
