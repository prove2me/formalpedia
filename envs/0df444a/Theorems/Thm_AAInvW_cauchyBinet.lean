-- Prove2me | Theorems.Thm_AAInvW_cauchyBinet
-- name    : AAInvW.cauchyBinet
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:27:13.790638+00:00
-- url     : https://prove2.me/theorems/00df17a1-ffe0-4e7c-bc48-4aff531ab78a
-- title:
--   AAInv W: cauchy Binet
-- statement:
--   The AAInv W construction uses the cauchy Binet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CauchyBinet.lean#L146-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CauchyBinet.lean#L146-L170

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

theorem AAInvW.cauchyBinet {m N : ℕ} (κ : Fin N → ℕ) (hκ : Function.Injective κ)
    (X : Matrix (Fin m) (Fin N) ℂ) (Y : Matrix (Fin N) (Fin m) ℂ) :
    (X * Y).det = ∑ C : Fin m → Fin N,
      if StrictMono (fun l => κ (C l)) then
        (Matrix.of fun a l => X a (C l)).det * (Matrix.of fun i l => Y (C i) l).det else 0 := by sorry
