-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_DensPf_map_C_mat
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.DensPf.map_C_mat
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:43:13.304031+00:00
-- url     : https://prove2.me/theorems/ce6cd69f-37b2-5524-a504-3a7952e66b79
-- title:
--   Dens Pf: map C mat
-- statement:
--   The Dens Pf construction uses the map C mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/CayleyIsometry.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/CayleyIsometry.lean#L64-L66

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_CayleyIsometry
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
open Matrix MvPolynomial
open scoped ComplexOrder
open Formalism.L2.SG.Pf.ColDictValCPf.DensPf
variable {n : ℕ}

theorem Formalism.L2.SG.Pf.ColDictValCPf.DensPf.map_C_mat (z : Bool × Fin n × Fin n → ℂ) (H : Matrix (Fin n) (Fin n) ℂ) :
    (eval z).mapMatrix (H.map C) = H := by sorry
