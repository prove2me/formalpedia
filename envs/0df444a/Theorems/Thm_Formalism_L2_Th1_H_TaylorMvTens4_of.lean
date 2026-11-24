-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_TaylorMvTens4_of
-- name    : Formalism.L2.Th1.H.TaylorMvTens4_of
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:23:32.478578+00:00
-- url     : https://prove2.me/theorems/be89a253-46ca-4e5f-a63c-e1f9e6318dbc
-- title:
--   H: Taylor Mv Tens4 of
-- statement:
--   The H construction uses the Taylor Mv Tens4 of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LineRestrLinSubst.lean#L174-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LineRestrLinSubst.lean#L174-L183

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LineRestrLinSubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open TMv Formalism.L2.Th1.F

theorem Formalism.L2.Th1.H.TaylorMvTens4_of (hU : LineUnique) (hL : TaylorLine) : TaylorMvTens4 := by sorry
