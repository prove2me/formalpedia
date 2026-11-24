-- Prove2me | Theorems.Thm_AAInvW_strictMono_val_iff
-- name    : AAInvW.strictMono_val_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:55:18.237813+00:00
-- url     : https://prove2.me/theorems/804618a9-dd5f-449d-b340-d588ce9ddb7b
-- title:
--   AAInv W: strict Mono val iff
-- statement:
--   The AAInv W construction uses the strict Mono val iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/DetTransposeApply.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/DetTransposeApply.lean#L36-L38

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OfFnProdSmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CauchyBinet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_DetTransposeApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem AAInvW.strictMono_val_iff {m N : ℕ} (C : Fin m → Fin N) :
    StrictMono (fun l => (C l).val) ↔ StrictMono C := by sorry
