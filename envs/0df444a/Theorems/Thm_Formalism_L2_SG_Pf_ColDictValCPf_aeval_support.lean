-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_aeval_support
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.aeval_support
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:32:59.389988+00:00
-- url     : https://prove2.me/theorems/b7020037-5532-4d39-8e6a-440deb639e2a
-- title:
--   Col Dict Val CPf: aeval support
-- statement:
--   The Col Dict Val CPf construction uses the aeval support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/HighExistenceHolds.lean#L75-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/HighExistenceHolds.lean#L75-L81

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

theorem Formalism.L2.SG.Pf.ColDictValCPf.aeval_support (w : σ → ℕ) (c : ℕ) (f : σ → Polynomial (MvPolynomial σ ℂ))
    (hf : ∀ v, TGood w c (w v) (f v)) (P : MvPolynomial σ ℂ) (j : ℕ) (m' : σ →₀ ℕ)
    (h : coeff m' ((aeval f P).coeff j) ≠ 0) :
    ∃ m, coeff m P ≠ 0 ∧ Finsupp.weight w m' + j * c = Finsupp.weight w m := by sorry
