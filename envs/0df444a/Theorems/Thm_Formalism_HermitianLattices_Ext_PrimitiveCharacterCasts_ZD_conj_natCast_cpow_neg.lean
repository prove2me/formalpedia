-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_conj_natCast_cpow_neg
-- name    : Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.conj_natCast_cpow_neg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:47.406823+00:00
-- url     : https://prove2.me/theorems/7879b5e8-30b5-459a-95a9-a28797943dae
-- title:
--   ZD: conj nat Cast cpow neg
-- statement:
--   The ZD construction uses the conj nat Cast cpow neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZBlock.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZBlock.lean#L15-L21

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZBlock
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

theorem Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.conj_natCast_cpow_neg (n : ℕ) (z : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (-z)) = (n : ℂ) ^ (-(starRingEnd ℂ) z) := by sorry
