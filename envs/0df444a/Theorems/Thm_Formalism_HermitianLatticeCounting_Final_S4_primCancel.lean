-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_Final_S4_primCancel
-- name    : Formalism.HermitianLatticeCounting.Final.S4.primCancel
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:36:49.709805+00:00
-- url     : https://prove2.me/theorems/6012578f-0032-52f7-9dcb-4a91f11f5ca7
-- title:
--   S4: prim Cancel
-- statement:
--   The S4 construction uses the prim Cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/ValuationProductBound.lean#L47-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/ValuationProductBound.lean#L47-L47

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.S4

theorem Formalism.HermitianLatticeCounting.Final.S4.primCancel : Formalism.HermitianLatticeCounting.S4.PrimCancel := by sorry
