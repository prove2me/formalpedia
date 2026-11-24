-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLevelIdx_kset_mul
-- name    : Formalism.MainNotions.BridgeLevelIdx.kset_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:41:41.455799+00:00
-- url     : https://prove2.me/theorems/714885d1-d915-4806-bbb0-913ab6e928b4
-- title:
--   Bridge Level Idx: kset mul
-- statement:
--   The Bridge Level Idx construction uses the kset mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelIdx.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelIdx.lean#L37-L40

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelIdx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelIdx
open MeasureTheory Formalism.MainNotions.S Matrix
open scoped ENNReal TensorProduct
variable (I : AutInst)
variable {I}

theorem Formalism.MainNotions.BridgeLevelIdx.kset_mul {x x' : I.Gf} (hx : x ∈ I.Kset) (hx' : x' ∈ I.Kset) : x⁻¹ * x' ∈ I.Kset := by sorry
