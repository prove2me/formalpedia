-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_lcomp_fix
-- name    : Formalism.CountingSumsFrames.lcomp_fix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:18.970258+00:00
-- url     : https://prove2.me/theorems/9ce91511-3562-4abb-8d34-138717dcf100
-- title:
--   Counting Sums Frames: lcomp fix
-- statement:
--   The Counting Sums Frames construction uses the lcomp fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1660-L1668
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1660-L1668

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

theorem Formalism.CountingSumsFrames.lcomp_fix {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι] (P : ι → V →ₗ[K] V)
    (hPP : ∀ j x, P j (P j x) = P j x) (hcomm : ∀ j j' x, P j (P j' x) = P j' (P j x)) :
    ∀ l : List ι, ∀ j ∈ l, ∀ u, P j (lcomp P l u) = lcomp P l u
  := by sorry
