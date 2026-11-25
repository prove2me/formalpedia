-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_Final_S4_moveAdm
-- name    : Formalism.HermitianLatticeCounting.Final.S4.moveAdm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:37:11.698614+00:00
-- url     : https://prove2.me/theorems/a663519a-9f50-42a0-a96d-80d308f19b5b
-- title:
--   S4: move Adm
-- statement:
--   The S4 construction uses the move Adm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/ValuationProductBound.lean#L38-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/ValuationProductBound.lean#L38-L38

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_moveAdm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.S4

theorem Formalism.HermitianLatticeCounting.Final.S4.moveAdm : Formalism.HermitianLatticeCounting.S4.MoveAdm := by sorry
