-- Prove2me | Theorems.Thm_AAInvW_det_mul_expand
-- name    : AAInvW.det_mul_expand
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:54:42.557139+00:00
-- url     : https://prove2.me/theorems/9c97db77-ec11-4cc3-ad95-709b840506ca
-- title:
--   AAInv W: det mul expand
-- statement:
--   The AAInv W construction uses the det mul expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CauchyBinet.lean#L130-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CauchyBinet.lean#L130-L144

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CauchyBinet
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

theorem AAInvW.det_mul_expand {m N : ℕ} (X : Matrix (Fin m) (Fin N) ℂ) (Y : Matrix (Fin N) (Fin m) ℂ) :
    (X * Y).det = ∑ d : Fin m → Fin N, (∏ l, Y (d l) l) • (Matrix.of fun a l => X a (d l)).det := by sorry
