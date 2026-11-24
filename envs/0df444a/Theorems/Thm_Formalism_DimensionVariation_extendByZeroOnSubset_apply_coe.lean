-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_extendByZeroOnSubset_apply_coe
-- name    : Formalism.DimensionVariation.extendByZeroOnSubset_apply_coe
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:43:47.080811+00:00
-- url     : https://prove2.me/theorems/2bec19cd-1a22-4737-bc0b-8d05628b73ec
-- title:
--   Dimension Variation: extend By Zero On Subset apply coe
-- statement:
--   The Dimension Variation construction uses the extend By Zero On Subset apply coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/DominanceMono.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/DominanceMono.lean#L9-L10

import Definitions.Def_Formalism_ThetaSupremumBounds_StatementB
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_DominanceMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.DimensionVariation

theorem Formalism.DimensionVariation.extendByZeroOnSubset_apply_coe {r : ℕ} (f : Fin r → ℝ) (i : Fin r) : ext0 f (i : ℕ) = f i := by sorry
