-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Rec_TraceQuadraticBound_quad_le_trace_HH
-- name    : Formalism.L2.Geo.Rec.TraceQuadraticBound.quad_le_trace_HH
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:53.661325+00:00
-- url     : https://prove2.me/theorems/4b934507-1acb-48db-a9f1-8abc38033bca
-- title:
--   Trace Quadratic Bound: quad le trace HH
-- statement:
--   The Trace Quadratic Bound construction uses the quad le trace HH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/ExistsStarMulSelf.lean#L36-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/ExistsStarMulSelf.lean#L36-L47

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Rec Formalism.L2.Geo.Rec.TraceQuadraticBound
variable {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.L2.Geo.Rec.TraceQuadraticBound.quad_le_trace_HH (H : Matrix n n ℂ) (w : n → ℂ) :
    (star w ⬝ᵥ (Hᴴ * H) *ᵥ w).re ≤ (Hᴴ * H).trace.re * ∑ i, ‖w i‖ ^ 2 := by sorry
