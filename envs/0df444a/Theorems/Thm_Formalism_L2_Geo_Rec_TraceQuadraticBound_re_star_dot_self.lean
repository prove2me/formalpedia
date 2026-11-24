-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Rec_TraceQuadraticBound_re_star_dot_self
-- name    : Formalism.L2.Geo.Rec.TraceQuadraticBound.re_star_dot_self
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:57.136254+00:00
-- url     : https://prove2.me/theorems/41a68dfa-73c9-4dde-9fa6-5224712fc546
-- title:
--   Trace Quadratic Bound: re star dot self
-- statement:
--   The Trace Quadratic Bound construction uses the re star dot self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/ExistsStarMulSelf.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/ExistsStarMulSelf.lean#L22-L26

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

theorem Formalism.L2.Geo.Rec.TraceQuadraticBound.re_star_dot_self (v : n → ℂ) : (star v ⬝ᵥ v).re = ∑ i, ‖v i‖ ^ 2 := by sorry
