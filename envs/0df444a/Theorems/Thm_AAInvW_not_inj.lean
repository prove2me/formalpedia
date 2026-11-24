-- Prove2me | Theorems.Thm_AAInvW_not_inj
-- name    : AAInvW.not_inj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:45:15.823951+00:00
-- url     : https://prove2.me/theorems/e2cc1a02-9255-4744-99e5-3600a6b91990
-- title:
--   AAInv W: not inj
-- statement:
--   The AAInv W construction uses the not inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/DetTransposeApply.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/DetTransposeApply.lean#L40-L44

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OfFnProdSmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CauchyBinet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_DetTransposeApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem AAInvW.not_inj {α β : Type*} {c : α → β} (hc : ¬ Function.Injective c) :
    ∃ p q, p ≠ q ∧ c p = c q := by sorry
