-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_tgood_prod
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.tgood_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:32:45.227794+00:00
-- url     : https://prove2.me/theorems/1fd2cfe0-ece7-4315-b1f2-201a49ea89c7
-- title:
--   Col Dict Val CPf: tgood prod
-- statement:
--   The Col Dict Val CPf construction uses the tgood prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/HighExistenceHolds.lean#L53-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/HighExistenceHolds.lean#L53-L62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighExistenceHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open MvPolynomial
variable {σ : Type*}

theorem Formalism.L2.SG.Pf.ColDictValCPf.tgood_prod {α : Type*} (w : σ → ℕ) (c : ℕ) (s : Finset α) (d : α → ℕ)
    (F : α → Polynomial (MvPolynomial σ ℂ)) (h : ∀ i ∈ s, TGood w c (d i) (F i)) :
    TGood w c (∑ i ∈ s, d i) (∏ i ∈ s, F i) := by sorry
