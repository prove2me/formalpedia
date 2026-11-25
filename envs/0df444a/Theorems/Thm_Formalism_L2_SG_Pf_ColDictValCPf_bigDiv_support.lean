-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_bigDiv_support
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.bigDiv_support
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:33:18.405599+00:00
-- url     : https://prove2.me/theorems/e69e8f85-1ebf-4d2b-81ee-413c1a6d4e52
-- title:
--   Col Dict Val CPf: big Div support
-- statement:
--   The Col Dict Val CPf construction uses the big Div support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/HighExistenceHolds.lean#L119-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/HighExistenceHolds.lean#L119-L124

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

theorem Formalism.L2.SG.Pf.ColDictValCPf.bigDiv_support {ι : Type} [DecidableEq ι] {n : ℕ} (τ : ι) (a b : Fin n) (hab : a < b) (k : ℕ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (m' : ι × Fin n × Fin n →₀ ℕ)
    (h : coeff m' (bigDiv τ a b k P) ≠ 0) :
    ∃ m, coeff m P ≠ 0 ∧ Finsupp.weight (fun v : ι × Fin n × Fin n => (v.2.1 : ℕ)) m' + k * ((b : ℕ) - a)
      = Finsupp.weight (fun v : ι × Fin n × Fin n => (v.2.1 : ℕ)) m := by sorry
