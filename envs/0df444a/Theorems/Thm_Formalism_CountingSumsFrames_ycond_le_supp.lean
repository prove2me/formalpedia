-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_ycond_le_supp
-- name    : Formalism.CountingSumsFrames.ycond_le_supp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:22.86582+00:00
-- url     : https://prove2.me/theorems/41da3d4a-0db3-4400-aca5-a5559369a1c0
-- title:
--   Counting Sums Frames: ycond le supp
-- statement:
--   The Counting Sums Frames construction uses the ycond le supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1197-L1199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1197-L1199

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

theorem Formalism.CountingSumsFrames.ycond_le_supp [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ) :
    YCond p (r := r) LL j Mt ≤ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by sorry
