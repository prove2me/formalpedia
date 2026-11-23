-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_wt_min
-- name    : Formalism.CountingSumsFrames.wt_min
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:34.64723+00:00
-- url     : https://prove2.me/theorems/33812643-f3fe-40dc-ba69-e2d8308368a8
-- title:
--   Counting Sums Frames: wt min
-- statement:
--   The Counting Sums Frames construction uses the wt min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1541-L1547
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1541-L1547

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

theorem Formalism.CountingSumsFrames.wt_min (LL : Letters N) (j : ℕ) (c : Fin r) : wt LL j c = wt LL (min j N) c := by sorry
