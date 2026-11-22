-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_glAct_pol
-- name    : Formalism.CountingSumsFrames.glAct_pol
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:23:33.607975+00:00
-- url     : https://prove2.me/theorems/6a62b003-3a6c-4973-b2fa-5d9ab16021f1
-- title:
--   Counting Sums Frames: gl Act pol
-- statement:
--   The Counting Sums Frames construction uses the gl Act pol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L667-L684
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L667-L684

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

theorem Formalism.CountingSumsFrames.glAct_pol (LL : Letters N) (j : ℕ) (c d : Fin r) :
    ∀ x ∈ Pol p r LL, glAct p LL j c d x ∈ Pol p r LL := by sorry
