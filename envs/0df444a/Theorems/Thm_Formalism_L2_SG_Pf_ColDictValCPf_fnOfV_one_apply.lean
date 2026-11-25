-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_fnOfV_one_apply
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.fnOfV_one_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:46:31.037227+00:00
-- url     : https://prove2.me/theorems/77c33ade-25e9-4274-bbc8-b580115e2430
-- title:
--   Col Dict Val CPf: fn Of V one apply
-- statement:
--   The Col Dict Val CPf construction uses the fn Of V one apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/IsUnitDetOfUnitary.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/IsUnitDetOfUnitary.lean#L15-L18

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

theorem Formalism.L2.SG.Pf.ColDictValCPf.fnOfV_one_apply (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (y : FramesV G) :
    fnOfV G s 1 P y = (∏ τ, (y.1 τ).det ^ s τ) * eval (fun x => y.1 x.1 x.2.1 x.2.2) P := by sorry
