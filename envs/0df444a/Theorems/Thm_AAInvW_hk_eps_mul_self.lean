-- Prove2me | Theorems.Thm_AAInvW_hk_eps_mul_self
-- name    : AAInvW.hk_eps_mul_self
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:54:57.714428+00:00
-- url     : https://prove2.me/theorems/679b94fd-163e-4b40-943b-09dc8f231a56
-- title:
--   AAInv W: hk eps mul self
-- statement:
--   The AAInv W construction uses the hk eps mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/HkConjTranspose.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/HkConjTranspose.lean#L32-L34

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

theorem AAInvW.hk_eps_mul_self (k r : ℕ) (i : Fin (2 * r + k + 1)) : hkEps k r i * hkEps k r i = 1 := by sorry
