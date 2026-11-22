-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_lcomp_cons
-- name    : Formalism.CountingSumsFrames.lcomp_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:23:46.084131+00:00
-- url     : https://prove2.me/theorems/0669810a-0995-4f0b-b087-f326ce112a5a
-- title:
--   Counting Sums Frames: lcomp cons
-- statement:
--   The Counting Sums Frames construction uses the lcomp cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L66-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L66-L66

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

theorem Formalism.CountingSumsFrames.lcomp_cons (φ : ι → V →ₗ[K] V) (i : ι) (l : List ι) : lcomp φ (i :: l) = φ i ∘ₗ lcomp φ l := by sorry
