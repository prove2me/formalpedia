-- Prove2me | Theorems.Thm_Formalism_GM_DetBound_gaussR_neg
-- name    : Formalism.GM.DetBound.gaussR_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:40.971375+00:00
-- url     : https://prove2.me/theorems/95ce365a-f9a1-4e5c-b1ba-1b783b16cee0
-- title:
--   Det Bound: gauss R neg
-- statement:
--   The Det Bound construction uses the gauss R neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L43-L44

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

theorem Formalism.GM.DetBound.gaussR_neg (ρ : NNReal) (P : K[X]) : gaussR ρ (-P) = gaussR ρ P := by sorry
