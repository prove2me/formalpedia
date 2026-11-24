-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_Aset_sum
-- name    : Formalism.MainNotions.PlaneGram.Aset_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:03:26.953166+00:00
-- url     : https://prove2.me/theorems/50494bd1-4e9b-43b7-877d-77d08ef95f32
-- title:
--   Plane Gram: Aset sum
-- statement:
--   The Plane Gram construction uses the Aset sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L185-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L185-L188

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
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
variable {K : Type} [Field K]

theorem Formalism.MainNotions.PlaneGram.Aset_sum {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L) (n : ℤ) {ι : Type}
    (s : Finset ι) (f : ι → MvPolynomial (L × Fin r) K) (h : ∀ i ∈ s, f i ∈ Aset sg S n) :
    ∑ i ∈ s, f i ∈ Aset sg S n := by sorry
