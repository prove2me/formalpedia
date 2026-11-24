-- Prove2me | Theorems.Thm_AAInvW_lf_esI_val
-- name    : AAInvW.lf_esI_val
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:45:49.09385+00:00
-- url     : https://prove2.me/theorems/2806f27e-499c-46bd-aad8-042fb1829d5a
-- title:
--   AAInv W: lf es I val
-- statement:
--   The AAInv W construction uses the lf es I val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SubsetUpperHessenberg.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SubsetUpperHessenberg.lean#L16-L16

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
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

theorem AAInvW.lf_esI_val (k r : ℕ) (a : Fin r) : (esI k r a).val = 2 * r + k - a.val := by sorry
