-- Prove2me | Theorems.Thm_Formalism_GM_DetBound_nnnorm_sum_mul_le
-- name    : Formalism.GM.DetBound.nnnorm_sum_mul_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:05.653122+00:00
-- url     : https://prove2.me/theorems/549d3230-13ca-4a9f-ad9e-ef28054effc5
-- title:
--   Det Bound: nnnorm sum mul le
-- statement:
--   The Det Bound construction uses the nnnorm sum mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L25-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L25-L35

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

theorem Formalism.GM.DetBound.nnnorm_sum_mul_le {ι : Type*} (s : Finset ι) (f : ι → K) (r b : NNReal)
    (h : ∀ i ∈ s, ‖f i‖₊ * r ≤ b) : ‖∑ i ∈ s, f i‖₊ * r ≤ b := by sorry
