-- Prove2me | Theorems.Thm_Formalism_SLP_P_CountO_count_prime_pow
-- name    : Formalism.SLP.P.CountO.count_prime_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:29:04.692048+00:00
-- url     : https://prove2.me/theorems/6ce06a74-d162-4976-9307-f7a48810cad5
-- title:
--   Count O: count prime pow
-- statement:
--   The Count O construction uses the count prime pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/CountO.lean#L433-L541
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/CountO.lean#L433-L541

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
open NumberField
variable (E : Type) [Field E] [NumberField E]
variable {E}

theorem Formalism.SLP.P.CountO.count_prime_pow (k p : ℕ) (hp : p.Prime) (e : ℕ) :
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X],
      TF E X → LIB E X k →
      (idxSet (𝓞 E) X (p ^ e)).Finite ∧
        (idxSet (𝓞 E) X (p ^ e)).ncard ≤ finrank ℚ E ^ e * (p ^ e) ^ k := by sorry
