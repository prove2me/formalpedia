-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGC_semi_genus_local
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z0.SGC.semi_genus_local
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:37:15.089488+00:00
-- url     : https://prove2.me/theorems/5a0c0793-2b31-4b98-a33f-2a3f6184d77e
-- title:
--   SGC: semi genus local
-- statement:
--   The SGC construction uses the semi genus local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/SemiGenusLocal.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/SemiGenusLocal.lean#L85-L88

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SelfDualRestr
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SemiGenusLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Module
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.SGC
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0.SGA Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.L2.SG.Pf.LatDictZ.Z0.SGC.semi_genus_local : SemiGenusLoc := by sorry
