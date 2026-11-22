-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_lower_action_preserves_weight_le
-- name    : Formalism.CountingSumsFrames.lower_action_preserves_weight_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:45:47.279093+00:00
-- url     : https://prove2.me/theorems/566cd7ed-7e59-463d-ba1f-6b3f20016e51
-- title:
--   Counting Sums Frames: lower action preserves weight le
-- statement:
--   The Counting Sums Frames construction uses the lower action preserves weight le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L857-L872
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L857-L872

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.lower_action_preserves_weight_le [NeZero r] (LL : Letters N) (j : ℕ) (c d : Fin r) (hdc : d < c) (Mt : WithTop ℤ) :
    ∀ x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt},
      glAct p LL j c d x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by sorry
