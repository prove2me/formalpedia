-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_phi_keeps
-- name    : Formalism.CountingSumsFrames.phi_keeps
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:45:58.292702+00:00
-- url     : https://prove2.me/theorems/d97fa55f-82e4-418d-a5f2-db95b68d497e
-- title:
--   Counting Sums Frames: phi keeps
-- statement:
--   The Counting Sums Frames construction uses the phi keeps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L443-L475
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L443-L475

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
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.CountingSumsFrames.phi_keeps {N r : ℕ} [NeZero r] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i j : Fin T.t)
    (hij : i < j) : ∀ u ∈ Y p (r := r) LL T.J (T.thrUpTo i), T.phi p LL j u ∈ Y p (r := r) LL T.J (T.thrUpTo i) := by sorry
