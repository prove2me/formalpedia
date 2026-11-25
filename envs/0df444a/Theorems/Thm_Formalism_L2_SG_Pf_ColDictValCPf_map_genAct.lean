-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_map_genAct
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.map_genAct
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:43:40.120344+00:00
-- url     : https://prove2.me/theorems/acd03e60-ceeb-52a8-ab1f-b7116b5dc328
-- title:
--   Col Dict Val CPf: map gen Act
-- statement:
--   The Col Dict Val CPf construction uses the map gen Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/DivisorClosedHolds.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/DivisorClosedHolds.lean#L30-L35

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

theorem Formalism.L2.SG.Pf.ColDictValCPf.map_genAct (τ : ι) (g : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    map (eval fun x => g x.1 x.2) (genAct τ P) = famAct (Function.update (fun _ => 1) τ g) P := by sorry
