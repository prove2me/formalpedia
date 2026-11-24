-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_neg_half_le_gExp
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.neg_half_le_gExp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:10.987475+00:00
-- url     : https://prove2.me/theorems/1bdb4319-61e6-4018-9bba-c810ed9a2067
-- title:
--   Supply AP: neg half le g Exp
-- statement:
--   The Supply AP construction uses the neg half le g Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffAbel.lean#L33-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffAbel.lean#L33-L41

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffAbel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP

theorem Formalism.HermitianLattices.Ext.SupplyAP.neg_half_le_gExp {t : ℝ} (ht : 0 < t) : -(1 / 2) ≤ gExp t := by sorry
