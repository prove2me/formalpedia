-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_mulLevel_apply
-- name    : Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.mulLevel_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:40.113821+00:00
-- url     : https://prove2.me/theorems/a60af7da-b477-49cb-a69b-1cab9968e5c0
-- title:
--   ZD: mul Level apply
-- statement:
--   The ZD construction uses the mul Level apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZPair.lean#L30-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZPair.lean#L30-L57

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

theorem Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.mulLevel_apply (p p' : PC) (n : ℕ) :
    mulLevel p p' (n : ZMod ((p.1 + 1) * (p'.1 + 1))) = cv p n * (starRingEnd ℂ) (cv p' n) := by sorry
