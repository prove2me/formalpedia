-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrd_ae_zero
-- name    : Formalism.MainNotions.LeviCoordinates.rrd_ae_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:27.062993+00:00
-- url     : https://prove2.me/theorems/3072f9f9-5fd9-4734-808b-73aae6c033d3
-- title:
--   Levi Coordinates: rrd ae zero
-- statement:
--   The Levi Coordinates construction uses the rrd ae zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrdStronglyMeasurable.lean#L133-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrdStronglyMeasurable.lean#L133-L198

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

theorem Formalism.MainNotions.LeviCoordinates.rrd_ae_zero [SigmaFinite μ] [IsLocallyFiniteMeasure μ] (ψ : G → ℂ) (hψ : StronglyMeasurable ψ) (M : ℝ)
    (hM : ∀ g, ‖ψ g‖ ≤ M) (h0 : ∀ f : G → ℂ, Continuous f → Integrable f μ → ∫ g, f g * ψ g ∂μ = 0) :
    ψ =ᵐ[μ] 0 := by sorry
