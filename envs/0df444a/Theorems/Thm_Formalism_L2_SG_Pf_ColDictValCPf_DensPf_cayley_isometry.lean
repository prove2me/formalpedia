-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_DensPf_cayley_isometry
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.DensPf.cayley_isometry
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:38:05.468485+00:00
-- url     : https://prove2.me/theorems/feb400a9-25e4-4339-855b-c5cf6c288cdb
-- title:
--   Dens Pf: cayley isometry
-- statement:
--   The Dens Pf construction uses the cayley isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/CayleyIsometry.lean#L15-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/CayleyIsometry.lean#L15-L35

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

theorem Formalism.L2.SG.Pf.ColDictValCPf.DensPf.cayley_isometry (G A : Matrix (Fin n) (Fin n) ℂ) (hskew : Aᴴ * G = -(G * A))
    (hB : IsUnit (1 + A).det) :
    ((1 - A) * (1 + A)⁻¹)ᴴ * G * ((1 - A) * (1 + A)⁻¹) = G := by sorry
