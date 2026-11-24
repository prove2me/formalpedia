-- Prove2me | Theorems.Thm_Formalism_HN_frame_linear_algebra_first
-- name    : Formalism.HN.frame_linear_algebra_first
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:13.552813+00:00
-- url     : https://prove2.me/theorems/653e28cf-f6d5-4157-bd8d-58df6c6bfc10
-- title:
--   HN: frame linear algebra first
-- statement:
--   The HN construction uses the frame linear algebra first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/FrameLinearAlgebraFirst.lean#L77-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/FrameLinearAlgebraFirst.lean#L77-L221

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_StatementFrameF
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_SumNormSqLeHilbertSchmidt
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameLinearAlgebraFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HN
open Finset Module LinearMap Formalism.CorankShareLayerCake.FR Formalism.CorankShareLayerCake.FR.Pgsn2pfrla PframeLA1
open scoped InnerProductSpace

theorem Formalism.HN.frame_linear_algebra_first : FrameLA1 := by sorry
