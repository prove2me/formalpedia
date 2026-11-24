-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_excBoundEff
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.excBoundEff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:51.027881+00:00
-- url     : https://prove2.me/theorems/ba8848ac-8a2f-4e03-a578-13b1ec9f6f2c
-- title:
--   Supply AP: exc Bound Eff
-- statement:
--   The Supply AP construction uses the exc Bound Eff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffExc.lean#L22-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffExc.lean#L22-L90

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_LfunctionOneLowerBound
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LDerivNearOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffExc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ZeroFreeDirichlet
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP

theorem Formalism.HermitianLattices.Ext.SupplyAP.excBoundEff : ExcBoundAt 2 := by sorry
