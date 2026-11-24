-- Prove2me | Theorems.Thm_Formalism_GM_DetBound_gaussR_prod_le
-- name    : Formalism.GM.DetBound.gaussR_prod_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:37.081116+00:00
-- url     : https://prove2.me/theorems/fcbe666d-06db-444c-ada6-91c011b46958
-- title:
--   Det Bound: gauss R prod le
-- statement:
--   The Det Bound construction uses the gauss R prod le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L65-L72

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

theorem Formalism.GM.DetBound.gaussR_prod_le {ι : Type*} (ρ : NNReal) (s : Finset ι) (f : ι → K[X]) :
    gaussR ρ (∏ i ∈ s, f i) ≤ ∏ i ∈ s, gaussR ρ (f i) := by sorry
