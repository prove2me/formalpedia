-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_taylorMv_prod
-- name    : Formalism.L2.Th1.H.taylorMv_prod
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:23:36.011841+00:00
-- url     : https://prove2.me/theorems/f5752146-cb17-4658-804f-853e28e0d150
-- title:
--   H: taylor Mv prod
-- statement:
--   The H construction uses the taylor Mv prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LineRestrLinSubst.lean#L154-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LineRestrLinSubst.lean#L154-L165

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

theorem Formalism.L2.Th1.H.taylorMv_prod (hU : LineUnique) (hL : TaylorLine) {n : Type} [Fintype n] [DecidableEq n]
    {ι : Type} (s : Finset ι) (F : ι → (n → ℂ) → ℂ) (hF : ∀ i, AnalyticAt ℂ (F i) 0) :
    taylorMv (fun z => ∏ i ∈ s, F i z) = ∏ i ∈ s, taylorMv (F i) := by sorry
