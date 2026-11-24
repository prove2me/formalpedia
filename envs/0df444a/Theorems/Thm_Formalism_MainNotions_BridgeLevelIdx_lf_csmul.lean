-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLevelIdx_lf_csmul
-- name    : Formalism.MainNotions.BridgeLevelIdx.lf_csmul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:40:45.327929+00:00
-- url     : https://prove2.me/theorems/ef48e45b-018d-47b5-a48a-48095299ed2f
-- title:
--   Bridge Level Idx: lf csmul
-- statement:
--   The Bridge Level Idx construction uses the lf csmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelIdx.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelIdx.lean#L21-L23

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

theorem Formalism.MainNotions.BridgeLevelIdx.lf_csmul (a : IntAf I.F I.E) {z : Fin I.n → I.E ⊗[I.F] Af I.F} (hz : z ∈ I.Lf) :
    (a : I.E ⊗[I.F] Af I.F) • z ∈ I.Lf := by sorry
