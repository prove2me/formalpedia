-- Prove2me | Theorems.Thm_Formalism_LT_TorsProof_eval_eq
-- name    : Formalism.LT.TorsProof.eval_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:52:07.579198+00:00
-- url     : https://prove2.me/theorems/c437fc08-69c0-42f8-936d-ec53873b46a5
-- title:
--   Tors Proof: eval eq
-- statement:
--   The Tors Proof construction uses the eval eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/TorsionNormIterProof.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/TorsionNormIterProof.lean#L24-L26

import Definitions.Def_Formalism_TorsionNormIteration_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_TorsionNormIterProof
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.LT Formalism.LT.TorsProof
open Polynomial
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
variable {π : K} {q : ℕ} {e : Polynomial K}

theorem Formalism.LT.TorsProof.eval_eq (e : Polynomial K) (x : K) :
    e.eval x = ∑ i ∈ Finset.range (e.natDegree + 1), e.coeff i * x ^ i := by sorry
