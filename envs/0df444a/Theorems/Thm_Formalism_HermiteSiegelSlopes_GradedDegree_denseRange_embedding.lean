-- Prove2me | Theorems.Thm_Formalism_HermiteSiegelSlopes_GradedDegree_denseRange_embedding
-- name    : Formalism.HermiteSiegelSlopes.GradedDegree.denseRange_embedding
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:37:44.09132+00:00
-- url     : https://prove2.me/theorems/ac47bb8e-4fc8-59d6-ad6c-0299f4231e9b
-- title:
--   Graded Degree: dense Range embedding
-- statement:
--   The Graded Degree construction uses the dense Range embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SubmoduleSlopeLowerOfFiltration.lean#L17-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SubmoduleSlopeLowerOfFiltration.lean#L17-L38

import Mathlib
import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_SpanMuMin
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SubmoduleSlopeLowerOfFiltration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open Formalism.HermiteSiegelSlopes.GradedDegree

theorem Formalism.HermiteSiegelSlopes.GradedDegree.denseRange_embedding {K : Type} [Field K] [NumberField K] (v : InfinitePlace K)
    (hv : v.IsComplex) : DenseRange (v.embedding : K → ℂ) := by sorry
