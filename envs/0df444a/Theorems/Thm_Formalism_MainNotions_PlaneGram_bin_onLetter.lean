-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_bin_onLetter
-- name    : Formalism.MainNotions.PlaneGram.bin_onLetter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:05:19.086594+00:00
-- url     : https://prove2.me/theorems/9a441a91-dd3d-449c-88f9-8b1405735643
-- title:
--   Plane Gram: bin on Letter
-- statement:
--   The Plane Gram construction uses the bin on Letter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L199-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L199-L210

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
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
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ}

theorem Formalism.MainNotions.PlaneGram.bin_onLetter (i : L) (M : Fin r →₀ ℕ) (α : L × Fin r →₀ ℕ) :
    (bin (onLetter i M) α : K) = bin M (letE α i) := by sorry
