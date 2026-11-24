-- Prove2me | Theorems.Thm_Formalism_REAL_rho_nsq_root
-- name    : Formalism.REAL.rho_nsq_root
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:24:28.519971+00:00
-- url     : https://prove2.me/theorems/f964854a-d051-44e0-9123-af69b954d5c0
-- title:
--   REAL: rho nsq root
-- statement:
--   The REAL construction uses the rho nsq root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/HalfSumRootsStandard.lean#L51-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/HalfSumRootsStandard.lean#L51-L63

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
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

theorem Formalism.REAL.rho_nsq_root {n : ℕ} (x : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b) :
    nsq (x + root a b) = nsq x + 2 * (x a - x b) + 2 := by sorry
