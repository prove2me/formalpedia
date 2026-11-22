-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_le_lord_sum
-- name    : Formalism.MainNotions.PlaneGram.le_lord_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:05:58.454976+00:00
-- url     : https://prove2.me/theorems/8d1f6631-47c9-4284-9774-f5592e5ac6c5
-- title:
--   Plane Gram: le lord sum
-- statement:
--   The Plane Gram construction uses the le lord sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L35-L43

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
variable {R : Type} [Semiring R]

theorem Formalism.MainNotions.PlaneGram.le_lord_sum {ι : Type} {n : WithTop ℤ} (s : Finset ι) (f : ι → LaurentPolynomial R)
    (h : ∀ i ∈ s, n ≤ lord (f i)) : n ≤ lord (∑ i ∈ s, f i) := by sorry
