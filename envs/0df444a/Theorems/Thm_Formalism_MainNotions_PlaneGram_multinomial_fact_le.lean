-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_multinomial_fact_le
-- name    : Formalism.MainNotions.PlaneGram.multinomial_fact_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:07:17.827812+00:00
-- url     : https://prove2.me/theorems/3c5b6851-f1ec-4cc0-ba63-7c15fce41039
-- title:
--   Plane Gram: multinomial fact le
-- statement:
--   The Plane Gram construction uses the multinomial fact le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L446-L460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L446-L460

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
variable {v} {p : ℕ} [CharZero K]

theorem Formalism.MainNotions.PlaneGram.multinomial_fact_le {ι : Type*} (q : ℕ) (f : ι → ℕ) (s : Finset ι) :
    (Nat.multinomial s f).factorization q ≤ s.card * Nat.log q (∑ i ∈ s, f i) := by sorry
