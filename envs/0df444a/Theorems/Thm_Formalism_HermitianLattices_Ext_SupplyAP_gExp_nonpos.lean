-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_gExp_nonpos
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.gExp_nonpos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:02.919422+00:00
-- url     : https://prove2.me/theorems/97171e21-f436-488e-a83c-de07ea1906f4
-- title:
--   Supply AP: g Exp nonpos
-- statement:
--   The Supply AP construction uses the g Exp nonpos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffAbel.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffAbel.lean#L8-L12

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

theorem Formalism.HermitianLattices.Ext.SupplyAP.gExp_nonpos {t : ℝ} (ht : 0 < t) : gExp t ≤ 0 := by sorry
