-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_pol_finiteDimensional
-- name    : Formalism.CountingSumsFrames.pol_finiteDimensional
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:22.399847+00:00
-- url     : https://prove2.me/theorems/d6a08475-e621-4e89-8b0a-c4cf3b6641b2
-- title:
--   Counting Sums Frames: pol finite Dimensional
-- statement:
--   The Counting Sums Frames construction uses the pol finite Dimensional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L150-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L150-L179

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
open Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.CountingSumsFrames.pol_finiteDimensional {N r : ℕ} (LL : Letters N) : FiniteDimensional ℚ_[p] (Pol p r LL) := by sorry
