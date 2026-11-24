-- Prove2me | Theorems.Thm_Formalism_L2_SG_AvgPf_avg_core
-- name    : Formalism.L2.SG.AvgPf.avg_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:58.103187+00:00
-- url     : https://prove2.me/theorems/688c5576-122a-42ea-b905-7f8f13ff7fbc
-- title:
--   Avg Pf: avg core
-- statement:
--   The Avg Pf construction uses the avg core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/LieAveraging/AvgCore.lean#L11-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/LieAveraging/AvgCore.lean#L11-L273

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_LieAveraging_LsSetresAvg
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_LieAveraging_AvgCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Set
open scoped Pointwise ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.AvgPf

theorem Formalism.L2.SG.AvgPf.avg_core (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (R Γ : Subgroup G) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (χ : G → ℂ) (f : G → V) (Ω : Set G)
    (hR : IsClosed (R : Set G)) (hΓR : Γ ≤ R) (hdisc : DiscreteTopology Γ)
    (hcpt : ∃ K : Set G, IsCompact K ∧ ∀ r ∈ R, ∃ s ∈ Γ, s * r ∈ K)
    (hχm : ∀ r ∈ R, ∀ r' ∈ R, χ (r * r') = χ r * χ r') (hχΓ : ∀ s ∈ Γ, χ s = 1)
    (hχne : ∃ r ∈ R, χ r ≠ 1) (hf : ∀ r ∈ R, ∀ x, f (r * x) = χ r • f x)
    (hΩ : MeasurableSet Ω ∧ (∀ x, ∃ s ∈ (Γ : Set G), s * x ∈ Ω) ∧
      ∀ x ∈ Ω, ∀ s ∈ (Γ : Set G), s * x ∈ Ω → s = 1) :
    ∫ x in Ω, f x ∂μ = 0 := by sorry
