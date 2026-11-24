-- Prove2me | Theorems.Thm_AAInvW_inv_mul_apply
-- name    : AAInvW.inv_mul_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:25:59.756056+00:00
-- url     : https://prove2.me/theorems/1113e71c-d776-4e8d-9f73-205f642cc60f
-- title:
--   AAInv W: inv mul apply
-- statement:
--   The AAInv W construction uses the inv mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OfFnProdIntertwine.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OfFnProdIntertwine.lean#L53-L56

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OpModel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_DetTransposeApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OfFnProdIntertwine
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

theorem AAInvW.inv_mul_apply {N : ℕ} (g s : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) (c : Fin N) :
    ((g * s)⁻¹ *ᵥ v) c = ∑ d, s⁻¹ c d * (g⁻¹ *ᵥ v) d := by sorry
