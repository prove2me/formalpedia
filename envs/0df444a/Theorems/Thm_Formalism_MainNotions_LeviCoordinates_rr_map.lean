-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_map
-- name    : Formalism.MainNotions.LeviCoordinates.rr_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:03.808287+00:00
-- url     : https://prove2.me/theorems/1e67eee4-494c-4bf0-8d5d-54ea72a3e4c7
-- title:
--   Levi Coordinates: rr map
-- statement:
--   The Levi Coordinates construction uses the rr map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrExistsMeasRep.lean#L214-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrExistsMeasRep.lean#L214-L224

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

theorem Formalism.MainNotions.LeviCoordinates.rr_map [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Countable Γ] (h : rr_FD μ Γ D) (g : G) :
    AEMeasurable (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D) ∧
      Measure.map (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D) = μ.restrict D := by sorry
