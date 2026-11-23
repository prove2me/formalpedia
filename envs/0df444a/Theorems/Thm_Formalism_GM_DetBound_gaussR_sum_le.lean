-- Prove2me | Theorems.Thm_Formalism_GM_DetBound_gaussR_sum_le
-- name    : Formalism.GM.DetBound.gaussR_sum_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:28.1678+00:00
-- url     : https://prove2.me/theorems/4714275b-aff7-4fe3-b253-7b9688f04787
-- title:
--   Det Bound: gauss R sum le
-- statement:
--   The Det Bound construction uses the gauss R sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L37-L41

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DetBound
open Finset Polynomial
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem Formalism.GM.DetBound.gaussR_sum_le {ι : Type*} (ρ : NNReal) (s : Finset ι) (f : ι → K[X]) (b : NNReal)
    (h : ∀ i ∈ s, gaussR ρ (f i) ≤ b) : gaussR ρ (∑ i ∈ s, f i) ≤ b := by sorry
