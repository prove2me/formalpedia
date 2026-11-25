-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_TMv_lineRestr_prod
-- name    : Formalism.L2.Th1.H.TMv.lineRestr_prod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:51:39.992785+00:00
-- url     : https://prove2.me/theorems/a793a024-483f-48ae-b6fe-7d61553f8773
-- title:
--   TMv: line Restr prod
-- statement:
--   The TMv construction uses the line Restr prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LineRestrLinSubst.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LineRestrLinSubst.lean#L42-L44

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
variable {K : Type*} [CommRing K] {n : Type*} [Finite n]

theorem Formalism.L2.Th1.H.TMv.lineRestr_prod {ι : Type*} (v : n → K) (s : Finset ι) (T : ι → MvPowerSeries n K) :
    lineRestr v (∏ i ∈ s, T i) = ∏ i ∈ s, lineRestr v (T i) := by sorry
