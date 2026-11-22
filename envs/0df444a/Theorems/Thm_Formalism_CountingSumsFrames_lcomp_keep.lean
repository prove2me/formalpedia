-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_lcomp_keep
-- name    : Formalism.CountingSumsFrames.lcomp_keep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:23:56.056788+00:00
-- url     : https://prove2.me/theorems/311ffa69-436e-49e5-a170-0e716696ba14
-- title:
--   Counting Sums Frames: lcomp keep
-- statement:
--   The Counting Sums Frames construction uses the lcomp keep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L68-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L68-L73

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
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι]

theorem Formalism.CountingSumsFrames.lcomp_keep (φ : ι → V →ₗ[K] V) (C : Set V) :
    ∀ l : List ι, (∀ j ∈ l, ∀ u ∈ C, φ j u ∈ C) → ∀ u ∈ C, lcomp φ l u ∈ C
  := by sorry
