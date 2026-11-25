-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_tgood_pow
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.tgood_pow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:39:56.861797+00:00
-- url     : https://prove2.me/theorems/45d55cc4-4b53-4dbc-97b2-8554096a1415
-- title:
--   Col Dict Val CPf: tgood pow
-- statement:
--   The Col Dict Val CPf construction uses the tgood pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/HighExistenceHolds.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/HighExistenceHolds.lean#L47-L51

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

theorem Formalism.L2.SG.Pf.ColDictValCPf.tgood_pow (w : σ → ℕ) (c : ℕ) {d : ℕ} {F : Polynomial (MvPolynomial σ ℂ)}
    (hF : TGood w c d F) (k : ℕ) : TGood w c (k * d) (F ^ k) := by sorry
