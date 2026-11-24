-- Prove2me | Theorems.Thm_AAInvW_lf_det_ne_zero
-- name    : AAInvW.lf_det_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:55:52.645395+00:00
-- url     : https://prove2.me/theorems/32346d34-1c06-4546-a3b4-a41d1868593b
-- title:
--   AAInv W: lf det ne zero
-- statement:
--   The AAInv W construction uses the lf det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SubsetUpperHessenberg.lean#L76-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SubsetUpperHessenberg.lean#L76-L87

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

theorem AAInvW.lf_det_ne_zero (k r : ℕ) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : inUH (Hpk k r) g) : g.det ≠ 0 := by sorry
