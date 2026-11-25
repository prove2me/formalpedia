-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G0_gam_le
-- name    : Formalism.InvariantFactorPaths.G0.gam_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:04.605642+00:00
-- url     : https://prove2.me/theorems/67599e6b-2618-5db0-888d-18eeab276d1b
-- title:
--   G0: gam le
-- statement:
--   The G0 construction uses the gam le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ProductIdealMonotone/ProductIdealProofs/LePowOddOfFloorLogbLe.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ProductIdealMonotone/ProductIdealProofs/LePowOddOfFloorLogbLe.lean#L11-L16

import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ParamDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ProductIdealProofs_LePowOddOfFloorLogbLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G0
variable {n : ℕ}

theorem Formalism.InvariantFactorPaths.G0.gam_le {p : ℝ} (hp : 5 ≤ p) : gam p ≤ 25 / (24 * p) := by sorry
