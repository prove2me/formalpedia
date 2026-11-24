-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G0_invariant_factors_submodule
-- name    : Formalism.InvariantFactorPaths.G0.invariant_factors_submodule
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:26.541964+00:00
-- url     : https://prove2.me/theorems/18128a44-1872-4c22-bf81-81a0915a38b3
-- title:
--   G0: invariant factors submodule
-- statement:
--   The G0 construction uses the invariant factors submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ProductIdealMonotone/ProductIdealProofs/ElementarySymmetricExpBound.lean#L13-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ProductIdealMonotone/ProductIdealProofs/ElementarySymmetricExpBound.lean#L13-L74

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

theorem Formalism.InvariantFactorPaths.G0.invariant_factors_submodule : InvariantFactorsSubmodule := by sorry
