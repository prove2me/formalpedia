-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_TMv_analyticAt_line0
-- name    : Formalism.L2.Th1.H.TMv.analyticAt_line0
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:24:54.072534+00:00
-- url     : https://prove2.me/theorems/36daf011-c59d-4caf-93e2-32c930e5f3d1
-- title:
--   TMv: analytic At line0
-- statement:
--   The TMv construction uses the analytic At line0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LineRestrLinSubst.lean#L109-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LineRestrLinSubst.lean#L109-L111

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

theorem Formalism.L2.Th1.H.TMv.analyticAt_line0 {F : (n → ℂ) → ℂ} (v : n → ℂ) (hF : AnalyticAt ℂ F 0) :
    AnalyticAt ℂ (fun t : ℂ => F (t • v)) 0 := by sorry
