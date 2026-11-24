-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Rec_TraceQuadraticBound_denseRange_emb
-- name    : Formalism.L2.Geo.Rec.TraceQuadraticBound.denseRange_emb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:44.893298+00:00
-- url     : https://prove2.me/theorems/1e45d68b-7a6a-4199-b159-1aa65ff35ca3
-- title:
--   Trace Quadratic Bound: dense Range emb
-- statement:
--   The Trace Quadratic Bound construction uses the dense Range emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/ExistsStarMulSelf.lean#L100-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/ExistsStarMulSelf.lean#L100-L114

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
variable {K : Type} [Field K]

theorem Formalism.L2.Geo.Rec.TraceQuadraticBound.denseRange_emb (σ : K →+* ℂ) (z : K) (hz : (σ z).im ≠ 0) : DenseRange σ := by sorry
