-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_projAtOf_of
-- name    : Formalism.InvariantFactorPaths.L4.projAtOf_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:57.715371+00:00
-- url     : https://prove2.me/theorems/9a74f97b-c9e4-484d-930f-5783dfe5ab44
-- title:
--   L4: proj At Of of
-- statement:
--   The L4 construction uses the proj At Of of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/GramBoundOfRestrictionOfProj.lean#L248-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/GramBoundOfRestrictionOfProj.lean#L248-L315

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_PartnerDeterminantHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundOfRestrictionOfProj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

theorem Formalism.InvariantFactorPaths.L4.projAtOf_of (hX : ProjX) : ProjAtOf := by sorry
