-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_as_sum
-- name    : Formalism.MainNotions.PlaneGram.ddiv_as_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:06:31.643941+00:00
-- url     : https://prove2.me/theorems/93f98199-530b-4825-b746-d523d0ef56ff
-- title:
--   Plane Gram: ddiv as sum
-- statement:
--   The Plane Gram construction uses the ddiv as sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L293-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L293-L299

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial

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
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} {I : Type} [Fintype I]

theorem Formalism.MainNotions.PlaneGram.ddiv_as_sum {σ : Type} (M : σ →₀ ℕ) (G : MvPolynomial σ K) :
    ddiv M G = ∑ α ∈ G.support, G.coeff α • ddiv M (monomial α (1 : K)) := by sorry
