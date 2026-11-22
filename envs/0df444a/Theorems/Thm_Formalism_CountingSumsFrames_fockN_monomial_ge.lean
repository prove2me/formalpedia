-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_fockN_monomial_ge
-- name    : Formalism.CountingSumsFrames.fockN_monomial_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:44:21.705819+00:00
-- url     : https://prove2.me/theorems/e73ac9d8-c1bb-45f9-baf7-5e1b086e72ec
-- title:
--   Counting Sums Frames: fock N monomial ge
-- statement:
--   The Counting Sums Frames construction uses the fock N monomial ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1614-L1648
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1614-L1648

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

theorem Formalism.CountingSumsFrames.fockN_monomial_ge (LL : Letters N) (z : MvPolynomial (Fin N × Fin r) ℚ_[p]) (m0 : Fin N × Fin r →₀ ℕ)
    (hm0 : MultiDeg LL m0) (hc : ‖coeff m0 z‖ = 1) : 1 ≤ ‖fockN p LL z (monomial m0 1)‖ := by sorry
