-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_exists_finset_card_gt
-- name    : Formalism.L2.LamCM.exists_finset_card_gt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:55.043395+00:00
-- url     : https://prove2.me/theorems/ed75d2a9-9c61-4b40-9674-00d8b05eee5f
-- title:
--   Lam CM: exists finset card gt
-- statement:
--   The Lam CM construction uses the exists finset card gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ExistsEvalNeZeroOfTotalDegreeLt.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ExistsEvalNeZeroOfTotalDegreeLt.lean#L18-L25

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsEvalNeZeroOfTotalDegreeLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open MvPolynomial IsLocalRing

theorem Formalism.L2.LamCM.exists_finset_card_gt {k : Type} (D : ℕ) (h : Infinite k ∨ D < Nat.card k) : ∃ S : Finset k, D < S.card := by sorry
