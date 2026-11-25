-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_eval_detBlocks
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.eval_detBlocks
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:38:27.829875+00:00
-- url     : https://prove2.me/theorems/c03949fc-0d85-4e73-b729-9bd080afe12a
-- title:
--   Col Dict Val CPf: eval det Blocks
-- statement:
--   The Col Dict Val CPf construction uses the eval det Blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/IsUnitDetOfUnitary.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/IsUnitDetOfUnitary.lean#L31-L38

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

theorem Formalism.L2.SG.Pf.ColDictValCPf.eval_detBlocks (x : ι × Fin n × Fin n → ℂ) :
    eval x (detBlocks (ι := ι) (n := n)) = ∏ τ, (Matrix.of fun a b : Fin n => x (τ, a, b)).det := by sorry
