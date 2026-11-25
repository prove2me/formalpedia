-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_Top_uKeepsLast
-- name    : Formalism.InvariantFactorPaths.L4.Top.uKeepsLast
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:55:36.062513+00:00
-- url     : https://prove2.me/theorems/90629349-f4f4-5aaa-8f28-80e4faeb0bcd
-- title:
--   Top: u Keeps Last
-- statement:
--   The Top construction uses the u Keeps Last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/MulEarlyModP.lean#L13-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/MulEarlyModP.lean#L13-L13

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundOfRestrictionOfProj
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResSat
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4 Formalism.InvariantFactorPaths.L4.Top
open Formalism.InvariantFactorPaths.L4

theorem Formalism.InvariantFactorPaths.L4.Top.uKeepsLast : UKeepsLast := by sorry
