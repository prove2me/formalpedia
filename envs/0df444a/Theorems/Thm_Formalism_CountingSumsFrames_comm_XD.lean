-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_comm_XD
-- name    : Formalism.CountingSumsFrames.comm_XD
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:37:50.818745+00:00
-- url     : https://prove2.me/theorems/64730805-b0c4-4c83-80d6-650b440542e8
-- title:
--   Counting Sums Frames: comm XD
-- statement:
--   The Counting Sums Frames construction uses the comm XD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L899-L909
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L899-L909

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
variable {k σ : Type} [Field k]

theorem Formalism.CountingSumsFrames.comm_XD [DecidableEq σ] (u v u' v' : σ) (g : MvPolynomial σ k) :
    X u * pderiv v (X u' * pderiv v' g) - X u' * pderiv v' (X u * pderiv v g) =
      (if u' = v then X u * pderiv v' g else 0) - (if u = v' then X u' * pderiv v g else 0) := by sorry
