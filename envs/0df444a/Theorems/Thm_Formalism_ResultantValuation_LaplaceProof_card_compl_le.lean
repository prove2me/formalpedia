-- Prove2me | Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_card_compl_le
-- name    : Formalism.ResultantValuation.LaplaceProof.card_compl_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:27:35.083023+00:00
-- url     : https://prove2.me/theorems/954dbcf7-907b-4a2c-9bc8-1813dca11198
-- title:
--   Laplace Proof: card compl le
-- statement:
--   The Laplace Proof construction uses the card compl le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Laplace.lean#L73-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Laplace.lean#L73-L84

import Definitions.Def_Formalism_ResultantValuation_ResultantConjugate
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Equiv
noncomputable section
open Formalism Formalism.ResultantValuation
open Formalism.ResultantValuation.LaplaceProof
variable {a b : ℕ}

theorem Formalism.ResultantValuation.LaplaceProof.card_compl_le (J : Finset (Fin (a + b))) (h : J.card = a) (i : Fin a) :
    (Jᶜ.filter (· ≤ J.orderEmbOfFin h i)).card + (i : ℕ) = (J.orderEmbOfFin h i : ℕ) := by sorry
