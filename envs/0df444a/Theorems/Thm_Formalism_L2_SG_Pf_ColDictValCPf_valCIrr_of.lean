-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_valCIrr_of
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.valCIrr_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:26:34.251352+00:00
-- url     : https://prove2.me/theorems/f06a7a8a-fef6-5d85-82c6-12a8b2bfc836
-- title:
--   Col Dict Val CPf: val CIrr of
-- statement:
--   The Col Dict Val CPf construction uses the val CIrr of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/DivClosedOf.lean#L68-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/DivClosedOf.lean#L68-L82

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ColDictValC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
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

theorem Formalism.L2.SG.Pf.ColDictValCPf.valCIrr_of (hT : Transfer) (hD : DivClosed) (hH : HiEx) (hU : Uniq) (hG : Gen) : ValCIrr := by sorry
