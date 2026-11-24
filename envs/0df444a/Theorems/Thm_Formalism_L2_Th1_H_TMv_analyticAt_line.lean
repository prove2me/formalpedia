-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_TMv_analyticAt_line
-- name    : Formalism.L2.Th1.H.TMv.analyticAt_line
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:24:46.164515+00:00
-- url     : https://prove2.me/theorems/d77a7d20-f7bd-4f01-88ed-7a4eef77dac1
-- title:
--   TMv: analytic At line
-- statement:
--   The TMv construction uses the analytic At line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LineRestrLinSubst.lean#L105-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LineRestrLinSubst.lean#L105-L107

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LineRestrLinSubst
import Theorems.Thm_Formalism_L2_Th1_F_taylorDeriv
import Theorems.Thm_Formalism_L2_Th1_F_taylorRing

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
open Formalism.L2.Th1.H.TMv
open Formalism.L2.Th1.F (taylor0 taylorRing taylorDeriv)
variable {n : Type} [Fintype n]

theorem Formalism.L2.Th1.H.TMv.analyticAt_line {F : (n → ℂ) → ℂ} {t₀ : ℂ} (v : n → ℂ) (hF : AnalyticAt ℂ F (t₀ • v)) :
    AnalyticAt ℂ (fun t : ℂ => F (t • v)) t₀ := by sorry
