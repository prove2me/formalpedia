-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_multiDeg_finite
-- name    : Formalism.CountingSumsFrames.multiDeg_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:45:39.204025+00:00
-- url     : https://prove2.me/theorems/5c46b4af-4849-4dd7-86b5-96b86dd4bbf3
-- title:
--   Counting Sums Frames: multi Deg finite
-- statement:
--   The Counting Sums Frames construction uses the multi Deg finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1430-L1444
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1430-L1444

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

theorem Formalism.CountingSumsFrames.multiDeg_finite (LL : Letters N) : ({m | MultiDeg (r := r) LL m} : Set (Fin N × Fin r →₀ ℕ)).Finite := by sorry
