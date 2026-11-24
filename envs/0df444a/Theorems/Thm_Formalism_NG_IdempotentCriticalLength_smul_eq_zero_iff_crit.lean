-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentCriticalLength_smul_eq_zero_iff_crit
-- name    : Formalism.NG.IdempotentCriticalLength.smul_eq_zero_iff_crit
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:14:06.797417+00:00
-- url     : https://prove2.me/theorems/6923f82f-41b9-4a0d-a4bb-5fa017a06015
-- title:
--   Idempotent Critical Length: smul eq zero iff crit
-- statement:
--   The Idempotent Critical Length construction uses the smul eq zero iff crit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SmulEqZeroIffCrit.lean#L23-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SmulEqZeroIffCrit.lean#L23-L50

import Definitions.Def_Formalism_CharacterColumnKernels_StatCompMultSimple
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEpsImgEqAdd
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SmulEqZeroIffCrit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdempotentCriticalLength
variable {O Λ : Type*} [CommRing O] [IsLocalRing O] [Ring Λ] [Algebra O Λ]

theorem Formalism.NG.IdempotentCriticalLength.smul_eq_zero_iff_crit {V : Type*} [AddCommGroup V] [Module Λ V] [IsSimpleModule Λ V]
    {ε : Λ} (hii : ∀ x : Λ, ∃ c : O, ε * x * ε - algebraMap O Λ c * ε ∈ Ring.jacobson Λ)
    (hiii : ∀ c ∈ IsLocalRing.maximalIdeal O, algebraMap O Λ c ∈ Ring.jacobson Λ)
    {v : V} (hv0 : v ≠ 0) (hv : ε • v = v) (x : Λ) :
    x • v = 0 ↔ Crit O ε x := by sorry
