-- Prove2me | Theorems.Thm_AAInvW_hk_mul_self
-- name    : AAInvW.hk_mul_self
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:55:17.05847+00:00
-- url     : https://prove2.me/theorems/64fb4955-d231-4bc3-ad7d-dfa84b43ad22
-- title:
--   AAInv W: hk mul self
-- statement:
--   The AAInv W construction uses the hk mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/HkConjTranspose.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/HkConjTranspose.lean#L40-L47

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
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

theorem AAInvW.hk_mul_self (k r : ℕ) : Hpk k r * Hpk k r = 1 := by sorry
