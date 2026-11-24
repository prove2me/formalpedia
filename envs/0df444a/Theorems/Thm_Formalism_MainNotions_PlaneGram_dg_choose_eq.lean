-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_choose_eq
-- name    : Formalism.MainNotions.PlaneGram.dg_choose_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:06:22.24019+00:00
-- url     : https://prove2.me/theorems/06dd041c-3817-4f2a-a7d6-935ec4ecc755
-- title:
--   Plane Gram: dg choose eq
-- statement:
--   The Plane Gram construction uses the dg choose eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1098-L1111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1098-L1111

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
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
variable {K : Type} [Field K] [CharZero K] {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} [NeZero r]
  {sg : L → Bool} {S : Finset L}
omit [CharZero K] [Fintype L] [NeZero r]

theorem Formalism.MainNotions.PlaneGram.dg_choose_eq {σ : Type} (x : σ) (k : ℕ) (F : MvPolynomial σ K) :
    dg (fun α => ((α x).choose k : K)) F =
      monomial (Finsupp.single x k) 1 * ddiv (Finsupp.single x k) F := by sorry
