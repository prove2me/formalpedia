-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_upper
-- name    : Formalism.MainNotions.PlaneGram.fact_upper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:05:27.81162+00:00
-- url     : https://prove2.me/theorems/2782245a-be15-483c-9e55-de846f808bb4
-- title:
--   Plane Gram: fact upper
-- statement:
--   The Plane Gram construction uses the fact upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L479-L483
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L479-L483

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

theorem Formalism.MainNotions.PlaneGram.fact_upper (hD : DVRHyp v p) {L : Type} [Fintype L] {r : ℕ}
    {α : L × Fin r →₀ ℕ} {d : L → ℕ} (h : ∀ i, ldeg α i = d i) :
    vN v (fact α) ≤ vN v (∏ i, (d i).factorial) := by sorry
