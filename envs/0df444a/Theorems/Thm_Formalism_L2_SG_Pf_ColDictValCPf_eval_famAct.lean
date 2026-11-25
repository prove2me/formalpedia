-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_eval_famAct
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.eval_famAct
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:38:36.144433+00:00
-- url     : https://prove2.me/theorems/0929c292-e3c7-49e3-bb76-2527dde6b0e8
-- title:
--   Col Dict Val CPf: eval fam Act
-- statement:
--   The Col Dict Val CPf construction uses the eval fam Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/IsUnitDetOfUnitary.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/IsUnitDetOfUnitary.lean#L20-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_IsUnitDetOfUnitary
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
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf Matrix MvPolynomial
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] {n : ℕ}

theorem Formalism.L2.SG.Pf.ColDictValCPf.eval_famAct (g : ι → Matrix (Fin n) (Fin n) ℂ) (x : ι × Fin n × Fin n → ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    eval x (famAct g P) = eval (fun v => ∑ c : Fin n, g v.1 v.2.1 c * x (v.1, c, v.2.2)) P := by sorry
