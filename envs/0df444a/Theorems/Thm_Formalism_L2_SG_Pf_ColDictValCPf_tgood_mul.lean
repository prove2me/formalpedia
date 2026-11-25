-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_tgood_mul
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.tgood_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:42:22.533295+00:00
-- url     : https://prove2.me/theorems/cb34518b-9e7a-53d8-b7fe-b3c959bd44c3
-- title:
--   Col Dict Val CPf: tgood mul
-- statement:
--   The Col Dict Val CPf construction uses the tgood mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/HighExistenceHolds.lean#L29-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/HighExistenceHolds.lean#L29-L41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighExistenceHolds
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
open MvPolynomial
variable {σ : Type*}

theorem Formalism.L2.SG.Pf.ColDictValCPf.tgood_mul (w : σ → ℕ) (c : ℕ) {d₁ d₂ : ℕ} {F G : Polynomial (MvPolynomial σ ℂ)}
    (hF : TGood w c d₁ F) (hG : TGood w c d₂ G) : TGood w c (d₁ + d₂) (F * G) := by sorry
