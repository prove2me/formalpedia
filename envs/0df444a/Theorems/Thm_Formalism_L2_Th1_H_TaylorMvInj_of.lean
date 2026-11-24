-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_TaylorMvInj_of
-- name    : Formalism.L2.Th1.H.TaylorMvInj_of
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:23:18.34975+00:00
-- url     : https://prove2.me/theorems/02b1df4e-3e48-4edd-b4d9-b9e99134fc74
-- title:
--   H: Taylor Mv Inj of
-- statement:
--   The H construction uses the Taylor Mv Inj of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LineRestrLinSubst.lean#L185-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LineRestrLinSubst.lean#L185-L196

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

theorem Formalism.L2.Th1.H.TaylorMvInj_of (_hU : LineUnique) (hL : TaylorLine) : TaylorMvInj := by sorry
