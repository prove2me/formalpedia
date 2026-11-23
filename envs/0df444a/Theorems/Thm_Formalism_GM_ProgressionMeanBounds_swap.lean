-- Prove2me | Theorems.Thm_Formalism_GM_ProgressionMeanBounds_swap
-- name    : Formalism.GM.ProgressionMeanBounds.swap
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:56.828632+00:00
-- url     : https://prove2.me/theorems/b0cbb505-4ab1-49dc-9bbb-8f086151203f
-- title:
--   Progression Mean Bounds: swap
-- statement:
--   The Progression Mean Bounds construction uses the swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowMeanAP.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowMeanAP.lean#L38-L42

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_DeterminantBlockLeadingTerm
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowMeanAP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Formalism.GM.ProgressionMeanBounds
open Finset Polynomial

theorem Formalism.GM.ProgressionMeanBounds.swap {K ι : Type} (W : Finset ι) (roots : Multiset K) (f : ι → K → ℝ) :
    ∑ t ∈ W, (roots.map (f t)).sum = (roots.map (fun ζ => ∑ t ∈ W, f t ζ)).sum := by sorry
