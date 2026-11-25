-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G0_almost_everywhere_spherical
-- name    : Formalism.InvariantFactorPaths.G0.almost_everywhere_spherical
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:11.318099+00:00
-- url     : https://prove2.me/theorems/a35689da-2a05-5710-acac-2580a19ca45d
-- title:
--   G0: almost everywhere spherical
-- statement:
--   The G0 construction uses the almost everywhere spherical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ProductIdealMonotone/ProductIdealProofs/ElementarySymmetricExpBound.lean#L145-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ProductIdealMonotone/ProductIdealProofs/ElementarySymmetricExpBound.lean#L145-L177

import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ElementarySymmetricExpBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ProductIdealProofs_LePowOddOfFloorLogbLe
import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ProductIdealProofs_ElementarySymmetricExpBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Pointwise
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G0
open Formalism.G0

theorem Formalism.InvariantFactorPaths.G0.almost_everywhere_spherical : AlmostEverywhereSpherical := by sorry
