-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Rec_TraceQuadraticBound_trace_nonneg
-- name    : Formalism.L2.Geo.Rec.TraceQuadraticBound.trace_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:46.55553+00:00
-- url     : https://prove2.me/theorems/768f5c60-e776-4c49-a4af-9985c2cff2e9
-- title:
--   Trace Quadratic Bound: trace nonneg
-- statement:
--   The Trace Quadratic Bound construction uses the trace nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/ExistsStarMulSelf.lean#L59-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/ExistsStarMulSelf.lean#L59-L67

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

theorem Formalism.L2.Geo.Rec.TraceQuadraticBound.trace_nonneg {b : Matrix n n ℂ} (hb : b.PosSemidef) (Y : Matrix n n ℂ) :
    0 ≤ (b * (Y * Yᴴ)).trace.re := by sorry
