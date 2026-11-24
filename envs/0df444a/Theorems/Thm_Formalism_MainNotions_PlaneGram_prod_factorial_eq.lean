-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_prod_factorial_eq
-- name    : Formalism.MainNotions.PlaneGram.prod_factorial_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:07:21.755268+00:00
-- url     : https://prove2.me/theorems/cde5c22f-0a7a-490d-8a50-911af35a1294
-- title:
--   Plane Gram: prod factorial eq
-- statement:
--   The Plane Gram construction uses the prod factorial eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L348-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L348-L355

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

theorem Formalism.MainNotions.PlaneGram.prod_factorial_eq {L : Type} [Fintype L] {r : ℕ} {α : L × Fin r →₀ ℕ} {d : L → ℕ}
    (h : ∀ i, ldeg α i = d i) :
    ∏ i, (d i).factorial = fact α * ∏ i : L, Nat.multinomial univ fun a : Fin r => α (i, a) := by sorry
