-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_eq_prod_letters
-- name    : Formalism.MainNotions.PlaneGram.fact_eq_prod_letters
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:09:05.255901+00:00
-- url     : https://prove2.me/theorems/58deeb54-7b69-4e57-8321-03779d20eb0c
-- title:
--   Plane Gram: fact eq prod letters
-- statement:
--   The Plane Gram construction uses the fact eq prod letters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L344-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L344-L346

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

theorem Formalism.MainNotions.PlaneGram.fact_eq_prod_letters {L : Type} [Fintype L] {r : ℕ} (α : L × Fin r →₀ ℕ) :
    fact α = ∏ i : L, ∏ a : Fin r, (α (i, a)).factorial := by sorry
