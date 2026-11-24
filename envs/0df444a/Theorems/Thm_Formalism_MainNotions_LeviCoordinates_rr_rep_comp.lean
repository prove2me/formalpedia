-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_rep_comp
-- name    : Formalism.MainNotions.LeviCoordinates.rr_rep_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:21.879752+00:00
-- url     : https://prove2.me/theorems/7a7e17bc-b606-4519-9c2e-5b077a71099b
-- title:
--   Levi Coordinates: rr rep comp
-- statement:
--   The Levi Coordinates construction uses the rr rep comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrExistsMeasRep.lean#L226-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrExistsMeasRep.lean#L226-L236

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
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
open MeasureTheory Set
open scoped ENNReal Pointwise InnerProductSpace
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
variable {μ : Measure G} {Γ : Subgroup G} {D : Set G}

theorem Formalism.MainNotions.LeviCoordinates.rr_rep_comp [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Countable Γ] (h : rr_FD μ Γ D) (g k : G) :
    ∀ᵐ x ∂μ, rr_rep (Γ : Set G) D (rr_rep (Γ : Set G) D (x * g) * k) = rr_rep (Γ : Set G) D (x * (g * k)) := by sorry
