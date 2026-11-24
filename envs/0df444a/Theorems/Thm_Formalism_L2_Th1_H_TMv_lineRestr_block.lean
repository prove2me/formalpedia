-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_TMv_lineRestr_block
-- name    : Formalism.L2.Th1.H.TMv.lineRestr_block
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:23:19.924866+00:00
-- url     : https://prove2.me/theorems/77c132c6-d2e8-451e-9c6a-a41b4987855d
-- title:
--   TMv: line Restr block
-- statement:
--   The TMv construction uses the line Restr block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LineRestrLinSubst.lean#L87-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LineRestrLinSubst.lean#L87-L99

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

theorem Formalism.L2.Th1.H.TMv.lineRestr_block {K : Type*} [CommRing K] {n : Type*} [Fintype n] (a : Fin 4)
    (v : Fin 4 × n → K) (T : MvPowerSeries n K) :
    lineRestr v (MvPowerSeries.subst
      (fun i => (MvPowerSeries.X (a, i) : MvPowerSeries (Fin 4 × n) K)) T)
      = lineRestr (fun i => v (a, i)) T := by sorry
