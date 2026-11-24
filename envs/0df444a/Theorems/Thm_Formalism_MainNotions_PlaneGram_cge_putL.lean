-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_putL
-- name    : Formalism.MainNotions.PlaneGram.cge_putL
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:06:51.803859+00:00
-- url     : https://prove2.me/theorems/de219e62-6e86-44d8-9760-71e874e5d966
-- title:
--   Plane Gram: cge put L
-- statement:
--   The Plane Gram construction uses the cge put L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L242-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L242-L247

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

theorem Formalism.MainNotions.PlaneGram.cge_putL (v : AddValuation K (WithTop ℚ)) (i : L) (α : L × Fin r →₀ ℕ) {a : ℝ}
    {Q : MvPolynomial (Fin r) K} (hQ : cge v a Q) : cge v a (putL i α Q) := by sorry
