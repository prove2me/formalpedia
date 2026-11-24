-- Prove2me | Theorems.Thm_Formalism_SLP_Final_sesqDet
-- name    : Formalism.SLP.Final.sesqDet
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:27:35.484479+00:00
-- url     : https://prove2.me/theorems/df3d6307-7871-438e-aa35-0ac2e6bb3e8b
-- title:
--   Final: sesq Det
-- statement:
--   The Final construction uses the sesq Det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SecondLevelArithmeticNorm.lean#L13-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SecondLevelArithmeticNorm.lean#L13-L13

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CardEqCardRangeNsmulMulCardKer
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SesquilinearDeterminantHolds
import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SubgroupCount
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_OmegaPow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DedekindLFunctions
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.Final

theorem Formalism.SLP.Final.sesqDet : Formalism.SLP.SesqDet := by sorry
