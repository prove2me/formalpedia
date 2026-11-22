-- Prove2me | Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_castAdd
-- name    : Formalism.ResultantValuation.LaplaceProof.shuffle_castAdd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:21:35.827963+00:00
-- url     : https://prove2.me/theorems/db4ddb3a-9e8f-4d51-b06b-9b01ab5a3a55
-- title:
--   Laplace Proof: shuffle cast Add
-- statement:
--   The Laplace Proof construction uses the shuffle cast Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Laplace.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Laplace.lean#L49-L51

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

theorem Formalism.ResultantValuation.LaplaceProof.shuffle_castAdd (J : Finset (Fin (a + b))) (h : J.card = a) (hc : Jᶜ.card = b)
    (i : Fin a) : shuffle J h hc (Fin.castAdd b i) = J.orderEmbOfFin h i := by sorry
