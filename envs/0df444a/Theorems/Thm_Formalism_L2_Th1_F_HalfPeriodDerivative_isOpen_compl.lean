-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_isOpen_compl
-- name    : Formalism.L2.Th1.F.HalfPeriodDerivative.isOpen_compl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:58:02.915458+00:00
-- url     : https://prove2.me/theorems/28a5fa82-8de1-4118-bdcd-543d3905e428
-- title:
--   Half Period Derivative: is Open compl
-- statement:
--   The Half Period Derivative construction uses the is Open compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/WeierstrassPSecondDerivative.lean#L15-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/WeierstrassPSecondDerivative.lean#L15-L15

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassPSecondDerivative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.HalfPeriodDerivative

theorem Formalism.L2.Th1.F.HalfPeriodDerivative.isOpen_compl (L : PeriodPair) : IsOpen ((L.lattice : Set ℂ)ᶜ) := by sorry
