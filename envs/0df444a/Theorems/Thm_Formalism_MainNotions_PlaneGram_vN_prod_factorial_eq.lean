-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vN_prod_factorial_eq
-- name    : Formalism.MainNotions.PlaneGram.vN_prod_factorial_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:46:04.786805+00:00
-- url     : https://prove2.me/theorems/2b44bedb-f419-4c91-a4ad-6aea178222b6
-- title:
--   Plane Gram: v N prod factorial eq
-- statement:
--   The Plane Gram construction uses the v N prod factorial eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L471-L477
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L471-L477

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

theorem Formalism.MainNotions.PlaneGram.vN_prod_factorial_eq (hD : DVRHyp v p) {L : Type} [Fintype L] {r : ℕ}
    {α : L × Fin r →₀ ℕ} {d : L → ℕ} (h : ∀ i, ldeg α i = d i) :
    vN v (∏ i, (d i).factorial) =
      vN v (fact α) + ∑ i : L, vN v (Nat.multinomial univ fun a : Fin r => α (i, a)) := by sorry
