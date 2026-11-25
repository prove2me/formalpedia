-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_DensPf_eval_hq
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.DensPf.eval_hq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:37:54.816169+00:00
-- url     : https://prove2.me/theorems/10a9928e-fa80-46c2-a2f7-3fe7df5514a4
-- title:
--   Dens Pf: eval hq
-- statement:
--   The Dens Pf construction uses the eval hq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/CayleyIsometry.lean#L82-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/CayleyIsometry.lean#L82-L105

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

theorem Formalism.L2.SG.Pf.ColDictValCPf.DensPf.eval_hq (G : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ)
    (z : Bool × Fin n × Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : (eval z).mapMatrix (Lp G) = A)
    (hd : det (1 + A) ≠ 0) :
    eval z (hq G p) = det (1 + A) ^ p.totalDegree *
      eval (fun x => ((1 - A) * (1 + A)⁻¹) x.1 x.2) p := by sorry
