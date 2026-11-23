-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrd_inner_vec
-- name    : Formalism.MainNotions.LeviCoordinates.rrd_inner_vec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:42:50.636341+00:00
-- url     : https://prove2.me/theorems/405c2956-8e5b-427a-82a9-a3e5c596d1d8
-- title:
--   Levi Coordinates: rrd inner vec
-- statement:
--   The Levi Coordinates construction uses the rrd inner vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrdStronglyMeasurable.lean#L247-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrdStronglyMeasurable.lean#L247-L253

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrdStronglyMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Filter Topology Set TopologicalSpace
open scoped InnerProductSpace
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SeparableSpace H]
variable {π : G → (H →L[ℂ] H)}

theorem Formalism.MainNotions.LeviCoordinates.rrd_inner_vec (hiso : ∀ g x, ‖π g x‖ = ‖x‖) (hmeas : ∀ x y, StronglyMeasurable fun g => ⟪x, π g y⟫_ℂ)
    {f : G → ℂ} (hf : Integrable f μ) (u v : H) : ⟪u, rrd_vec μ π f v⟫_ℂ = ∫ g, f g * ⟪u, π g v⟫_ℂ ∂μ := by sorry
