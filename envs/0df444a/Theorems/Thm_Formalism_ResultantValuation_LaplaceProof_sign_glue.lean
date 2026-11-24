-- Prove2me | Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_sign_glue
-- name    : Formalism.ResultantValuation.LaplaceProof.sign_glue
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:27:42.840741+00:00
-- url     : https://prove2.me/theorems/1b3150c3-8dfc-4240-97a2-63890519ef89
-- title:
--   Laplace Proof: sign glue
-- statement:
--   The Laplace Proof construction uses the sign glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Laplace.lean#L200-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Laplace.lean#L200-L204

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

theorem Formalism.ResultantValuation.LaplaceProof.sign_glue (x : Σ _ : {J : Finset (Fin (a + b)) // J.card = a},
    Perm (Fin a) × Perm (Fin b)) :
    Perm.sign (glue x) = (-1) ^ (a * (a - 1) / 2 + ∑ j ∈ x.1.1, (j : ℕ)) *
      Perm.sign x.2.1 * Perm.sign x.2.2 := by sorry
