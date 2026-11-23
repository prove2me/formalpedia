-- Prove2me | Theorems.Thm_Formalism_FN_gjZero
-- name    : Formalism.FN.gjZero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:02.400807+00:00
-- url     : https://prove2.me/theorems/7752845e-a849-4d2b-aca0-237a956b112a
-- title:
--   FN: gj Zero
-- statement:
--   The FN construction uses the gj Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/MinkCore.lean#L23-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/MinkCore.lean#L23-L38

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_MinkCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN

theorem Formalism.FN.gjZero (n : ℕ) (A : Set (Fin n → ℝ)) : Gj n 0 A = volume A := by sorry
