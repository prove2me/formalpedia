-- Prove2me | Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_perm_sign_eq_inversion_sign
-- name    : Formalism.ResultantValuation.LaplaceProof.perm_sign_eq_inversion_sign
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:27:38.125941+00:00
-- url     : https://prove2.me/theorems/5f0ea9c2-30ba-4903-97d4-f86ff90b976e
-- title:
--   Laplace Proof: perm sign eq inversion sign
-- statement:
--   The Laplace Proof construction uses the perm sign eq inversion sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Laplace.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Laplace.lean#L11-L15

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

theorem Formalism.ResultantValuation.LaplaceProof.perm_sign_eq_inversion_sign {n : ℕ} (f : Perm (Fin n)) : Perm.sign f = Perm.signAux f := by sorry
