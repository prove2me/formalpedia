-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_famAct_elem
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.famAct_elem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:27:30.038434+00:00
-- url     : https://prove2.me/theorems/11339c65-6a21-48e9-9b99-0c1b6f91da87
-- title:
--   Col Dict Val CPf: fam Act elem
-- statement:
--   The Col Dict Val CPf construction uses the fam Act elem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/DivisorClosedHolds.lean#L82-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/DivisorClosedHolds.lean#L82-L87

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivisorClosedHolds
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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem Formalism.L2.SG.Pf.ColDictValCPf.famAct_elem (τ : ι) (a b : Fin n) (t : ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    famAct (Function.update (fun _ => 1) τ (elem a b t)) P = (bigGen τ a b P).eval (C t) := by sorry
