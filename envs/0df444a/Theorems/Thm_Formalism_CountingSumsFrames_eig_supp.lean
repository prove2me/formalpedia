-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_eig_supp
-- name    : Formalism.CountingSumsFrames.eig_supp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:18.168704+00:00
-- url     : https://prove2.me/theorems/b174057f-5e37-4e6f-9cf1-884232509f28
-- title:
--   Counting Sums Frames: eig supp
-- statement:
--   The Counting Sums Frames construction uses the eig supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L786-L796
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L786-L796

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

theorem Formalism.CountingSumsFrames.eig_supp (LL : Letters N) (j : ℕ) (c : Fin r) (k : ℤ) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hy : glAct p LL j c c y = ((k : ℤ) : ℚ_[p]) • y) :
    y ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | wt LL j c m = k} := by sorry
