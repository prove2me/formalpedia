-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Rec_TraceQuadraticBound_norm_sum_sq_le
-- name    : Formalism.L2.Geo.Rec.TraceQuadraticBound.norm_sum_sq_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:44.183372+00:00
-- url     : https://prove2.me/theorems/683fff73-2234-42c3-b5e7-223bc0196f07
-- title:
--   Trace Quadratic Bound: norm sum sq le
-- statement:
--   The Trace Quadratic Bound construction uses the norm sum sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/ExistsStarMulSelf.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/ExistsStarMulSelf.lean#L28-L34

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

theorem Formalism.L2.Geo.Rec.TraceQuadraticBound.norm_sum_sq_le (a w : n → ℂ) : ‖∑ k, a k * w k‖ ^ 2 ≤ (∑ k, ‖a k‖ ^ 2) * ∑ k, ‖w k‖ ^ 2 := by sorry
