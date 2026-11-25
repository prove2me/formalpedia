-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_Final_S4_tauLin
-- name    : Formalism.HermitianLatticeCounting.Final.S4.tauLin
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:39:44.415858+00:00
-- url     : https://prove2.me/theorems/8cc5c27f-7ec4-5cb5-bcf6-1f94a2a15dff
-- title:
--   S4: tau Lin
-- statement:
--   The S4 construction uses the tau Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/ValuationProductBound.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/ValuationProductBound.lean#L14-L14

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_tauLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.S4

theorem Formalism.HermitianLatticeCounting.Final.S4.tauLin : Formalism.HermitianLatticeCounting.S4.TauLin := by sorry
