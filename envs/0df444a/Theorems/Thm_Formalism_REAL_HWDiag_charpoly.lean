-- Prove2me | Theorems.Thm_Formalism_REAL_HWDiag_charpoly
-- name    : Formalism.REAL.HWDiag_charpoly
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:19:48.9371+00:00
-- url     : https://prove2.me/theorems/ef3fa6b0-2c7c-4c64-a95f-a42eda5667d9
-- title:
--   REAL: HWDiag charpoly
-- statement:
--   The REAL construction uses the HWDiag charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/HWDiag.lean#L170-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/HWDiag.lean#L170-L183

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HWDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.HWDiag_charpoly {n : ℕ} (l : Fin n → ℂ) :
    (Amat l).charpoly = ∏ s : Fin n, (Polynomial.X - Polynomial.C (l s)) := by sorry
