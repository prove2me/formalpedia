-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrd_vec_tendsto
-- name    : Formalism.MainNotions.LeviCoordinates.rrd_vec_tendsto
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:56:52.344181+00:00
-- url     : https://prove2.me/theorems/bb240db6-4fe4-416c-b70a-7de0ff48f2bf
-- title:
--   Levi Coordinates: rrd vec tendsto
-- statement:
--   The Levi Coordinates construction uses the rrd vec tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrdStronglyMeasurable.lean#L229-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrdStronglyMeasurable.lean#L229-L245

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

theorem Formalism.MainNotions.LeviCoordinates.rrd_vec_tendsto (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hiso : ∀ g x, ‖π g x‖ = ‖x‖)
    (hmeas : ∀ x y, StronglyMeasurable fun g => ⟪x, π g y⟫_ℂ) {f : G → ℂ} (hc : Continuous f) (hf : Integrable f μ)
    (v : H) : Tendsto (fun h => π h (rrd_vec μ π f v)) (𝓝 1) (𝓝 (rrd_vec μ π f v)) := by sorry
