-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_wt_eq
-- name    : Formalism.CountingSumsFrames.wt_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:48:23.298512+00:00
-- url     : https://prove2.me/theorems/deead817-4781-41dd-963a-cb9413a1916b
-- title:
--   Counting Sums Frames: wt eq
-- statement:
--   The Counting Sums Frames construction uses the wt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L686-L690
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L686-L690

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

theorem Formalism.CountingSumsFrames.wt_eq (LL : Letters N) (j : ℕ) (c : Fin r) (m : Fin N × Fin r →₀ ℕ) :
    wt LL j c m = ∑ i : Fin N, (if (i : ℕ) < j then (if LL.vec i then (1 : ℤ) else -1) else 0) * (m (i, c) : ℤ) := by sorry
