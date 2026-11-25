-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_DensPf_skew_of
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.DensPf.skew_of
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:43:19.833682+00:00
-- url     : https://prove2.me/theorems/2c8a39fa-5061-5d49-9675-246cc39aaeff
-- title:
--   Dens Pf: skew of
-- statement:
--   The Dens Pf construction uses the skew of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/CayleyIsometry.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/CayleyIsometry.lean#L37-L43

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

theorem Formalism.L2.SG.Pf.ColDictValCPf.DensPf.skew_of (G P : Matrix (Fin n) (Fin n) ℂ) (hH : Gᴴ = G) (hG : IsUnit G.det) :
    (P - G⁻¹ * Pᴴ * G)ᴴ * G = -(G * (P - G⁻¹ * Pᴴ * G)) := by sorry
