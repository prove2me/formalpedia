-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_fnOfV_injective
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.fnOfV_injective
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:38:50.86137+00:00
-- url     : https://prove2.me/theorems/8bd1f44f-1467-4ee8-949a-ab828db80b40
-- title:
--   Col Dict Val CPf: fn Of V injective
-- statement:
--   The Col Dict Val CPf construction uses the fn Of V injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/IsUnitDetOfUnitary.lean#L50-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/IsUnitDetOfUnitary.lean#L50-L68

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

theorem Formalism.L2.SG.Pf.ColDictValCPf.fnOfV_injective (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (h : fnOfV G s 1 P = 0) : P = 0 := by sorry
