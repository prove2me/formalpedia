-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_glAct_min
-- name    : Formalism.CountingSumsFrames.glAct_min
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:46.49384+00:00
-- url     : https://prove2.me/theorems/6e26292c-2867-423e-b1d9-d42a23fb8849
-- title:
--   Counting Sums Frames: gl Act min
-- statement:
--   The Counting Sums Frames construction uses the gl Act min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1534-L1539
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1534-L1539

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

theorem Formalism.CountingSumsFrames.glAct_min (LL : Letters N) (j : ℕ) (c d : Fin r) : glAct p LL j c d = glAct p LL (min j N) c d := by sorry
