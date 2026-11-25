-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_Final_S4_equalityNG
-- name    : Formalism.HermitianLatticeCounting.Final.S4.equalityNG
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:37:10.550577+00:00
-- url     : https://prove2.me/theorems/cf16ff44-d639-4d86-8d15-c0a4025bcc9d
-- title:
--   S4: equality NG
-- statement:
--   The S4 construction uses the equality NG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/ValuationProductBound.lean#L64-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/ValuationProductBound.lean#L64-L64

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_equalityNG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.S4

theorem Formalism.HermitianLatticeCounting.Final.S4.equalityNG : Formalism.HermitianLatticeCounting.S4.EqualityNG := by sorry
