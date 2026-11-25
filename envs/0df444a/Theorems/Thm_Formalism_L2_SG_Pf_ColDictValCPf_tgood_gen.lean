-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_tgood_gen
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.tgood_gen
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:32:45.31814+00:00
-- url     : https://prove2.me/theorems/e02b4d3a-a32d-4a55-83f6-036075f02065
-- title:
--   Col Dict Val CPf: tgood gen
-- statement:
--   The Col Dict Val CPf construction uses the tgood gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/HighExistenceHolds.lean#L85-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/HighExistenceHolds.lean#L85-L117

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

theorem Formalism.L2.SG.Pf.ColDictValCPf.tgood_gen {ι : Type} [DecidableEq ι] {n : ℕ} (τ : ι) (a b : Fin n) (hab : a < b)
    (v : ι × Fin n × Fin n) :
    TGood (fun v : ι × Fin n × Fin n => (v.2.1 : ℕ)) ((b : ℕ) - a) (v.2.1 : ℕ)
      (Polynomial.C (X v) + (if v.1 = τ ∧ v.2.1 = b then Polynomial.X * Polynomial.C (X (τ, a, v.2.2))
        else 0)) := by sorry
