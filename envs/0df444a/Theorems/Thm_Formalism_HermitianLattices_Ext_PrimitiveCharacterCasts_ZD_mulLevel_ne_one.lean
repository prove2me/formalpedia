-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_mulLevel_ne_one
-- name    : Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.mulLevel_ne_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:16.917415+00:00
-- url     : https://prove2.me/theorems/40e76c1b-3f79-4f45-a498-a373b201dbcf
-- title:
--   ZD: mul Level ne one
-- statement:
--   The ZD construction uses the mul Level ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZPair.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZPair.lean#L15-L28

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

theorem Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.mulLevel_ne_one (p p' : PC) (hp : p.2.IsPrimitive) (hp' : p'.2.IsPrimitive) (hne : p ≠ p') :
    mulLevel p p' ≠ 1 := by sorry
