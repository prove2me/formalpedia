-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Rec_TraceQuadraticBound_quad_le_trace
-- name    : Formalism.L2.Geo.Rec.TraceQuadraticBound.quad_le_trace
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:47.145985+00:00
-- url     : https://prove2.me/theorems/15110186-5fef-4132-a9f7-419b29edd74a
-- title:
--   Trace Quadratic Bound: quad le trace
-- statement:
--   The Trace Quadratic Bound construction uses the quad le trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/ExistsStarMulSelf.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/ExistsStarMulSelf.lean#L49-L57

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

theorem Formalism.L2.Geo.Rec.TraceQuadraticBound.quad_le_trace {b : Matrix n n ℂ} (hb : b.PosSemidef) (Y : Matrix n n ℂ) (w : n → ℂ) :
    (star (Y *ᵥ w) ⬝ᵥ b *ᵥ (Y *ᵥ w)).re ≤ (b * (Y * Yᴴ)).trace.re * ∑ i, ‖w i‖ ^ 2 := by sorry
