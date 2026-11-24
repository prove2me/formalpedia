-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLevelIdx_kset_inv_mulVec
-- name    : Formalism.MainNotions.BridgeLevelIdx.kset_inv_mulVec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:41:42.4698+00:00
-- url     : https://prove2.me/theorems/19b71ae9-23be-4a73-8066-720dab41e240
-- title:
--   Bridge Level Idx: kset inv mul Vec
-- statement:
--   The Bridge Level Idx construction uses the kset inv mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelIdx.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelIdx.lean#L29-L35

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

theorem Formalism.MainNotions.BridgeLevelIdx.kset_inv_mulVec {x : I.Gf} (hx : x ∈ I.Kset) {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    I.fmat x⁻¹ *ᵥ y ∈ I.Lf := by sorry
