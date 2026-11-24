-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_pj_dens_real
-- name    : Formalism.MainNotions.LeviCoordinates.pj_dens_real
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T09:56:55.258248+00:00
-- url     : https://prove2.me/theorems/9b1f24e4-7440-4eb0-a0e1-152903e2aa5b
-- title:
--   Levi Coordinates: pj dens real
-- statement:
--   The Levi Coordinates construction uses the pj dens real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/PjDensUpper.lean#L10-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/PjDensUpper.lean#L10-L26

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_PjDensUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

theorem Formalism.MainNotions.LeviCoordinates.pj_dens_real (t p q r : ℝ) (ht : 0 < t) :
    (p + q + r) ^ 2 ≤ (1 + t) * p ^ 2 + (1 + 1 / t) * (2 * q ^ 2 + 2 * r ^ 2) := by sorry
