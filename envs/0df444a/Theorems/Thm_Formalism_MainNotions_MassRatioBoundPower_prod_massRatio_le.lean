-- Prove2me | Theorems.Thm_Formalism_MainNotions_MassRatioBoundPower_prod_massRatio_le
-- name    : Formalism.MainNotions.MassRatioBoundPower.prod_massRatio_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:17:41.297899+00:00
-- url     : https://prove2.me/theorems/0b0b99f7-2c86-43a7-a624-18236b78413e
-- title:
--   Mass Ratio Bound Power: prod mass Ratio le
-- statement:
--   The Mass Ratio Bound Power construction uses the prod mass Ratio le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/MassRatioBoundPower.lean#L69-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/MassRatioBoundPower.lean#L69-L81

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBoundPower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioBoundPower
open NumberField Formalism.MainNotions.MassRatioZetaBound
variable {K : Type*} [Field K] [NumberField K]

theorem Formalism.MainNotions.MassRatioBoundPower.prod_massRatio_le [StarRing K] (hd : Module.finrank ℚ K ≤ 2 * Formalism.HermitianLatticesTheory.fDeg K) (n : ℕ) {Y : ℝ} (hY : 2 ≤ Y)
    (hn : (n : ℝ) ≤ Y) (hv : 2 * Formalism.HermitianLatticesTheory.vInv K ≤ Y) :
    ∏ M ∈ Finset.Icc 3 n, Formalism.HermitianLatticesTheory.massRatioRightSide K M ≤ Y ^ ((2 * n + cZ) * n * Formalism.HermitianLatticesTheory.fDeg K) := by sorry
