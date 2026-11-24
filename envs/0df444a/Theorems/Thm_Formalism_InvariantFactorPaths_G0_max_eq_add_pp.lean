-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G0_max_eq_add_pp
-- name    : Formalism.InvariantFactorPaths.G0.max_eq_add_pp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:19.236317+00:00
-- url     : https://prove2.me/theorems/19d8de52-2cc0-4e03-a095-f54b7e88c633
-- title:
--   G0: max eq add pp
-- statement:
--   The G0 construction uses the max eq add pp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ProductIdealMonotone/ProductIdealProofs/ElementarySymmetricExpBound.lean#L105-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ProductIdealMonotone/ProductIdealProofs/ElementarySymmetricExpBound.lean#L105-L111

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

theorem Formalism.InvariantFactorPaths.G0.max_eq_add_pp (x y : ℝ) : max x y = y + pp (x - y) := by sorry
