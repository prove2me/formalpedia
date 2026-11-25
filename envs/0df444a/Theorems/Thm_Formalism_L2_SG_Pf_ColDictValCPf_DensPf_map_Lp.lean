-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_DensPf_map_Lp
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.DensPf.map_Lp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:43:27.129584+00:00
-- url     : https://prove2.me/theorems/ad4b9b28-d11f-5da3-9f70-52be73753d25
-- title:
--   Dens Pf: map Lp
-- statement:
--   The Dens Pf construction uses the map Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/CayleyIsometry.lean#L68-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/CayleyIsometry.lean#L68-L76

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

theorem Formalism.L2.SG.Pf.ColDictValCPf.DensPf.map_Lp (G : Matrix (Fin n) (Fin n) ℂ) (z : Bool × Fin n × Fin n → ℂ) :
    (eval z).mapMatrix (Lp G) =
      Matrix.of (fun i j => z (true, i, j) + Complex.I * z (false, i, j)) -
        G⁻¹ * Matrix.of (fun i j => z (true, j, i) - Complex.I * z (false, j, i)) * G := by sorry
