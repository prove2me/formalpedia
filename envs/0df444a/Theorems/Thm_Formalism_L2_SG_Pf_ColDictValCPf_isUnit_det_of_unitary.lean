-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_isUnit_det_of_unitary
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.isUnit_det_of_unitary
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:38:39.247051+00:00
-- url     : https://prove2.me/theorems/0038df26-f802-4e59-a407-adfeee69c66a
-- title:
--   Col Dict Val CPf: is Unit det of unitary
-- statement:
--   The Col Dict Val CPf construction uses the is Unit det of unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/IsUnitDetOfUnitary.lean#L70-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/IsUnitDetOfUnitary.lean#L70-L84

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

theorem Formalism.L2.SG.Pf.ColDictValCPf.isUnit_det_of_unitary {G g : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef ∨ (-G).PosDef)
    (hg : gᴴ * G * g = G) : IsUnit g.det := by sorry
