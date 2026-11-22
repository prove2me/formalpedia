-- Prove2me | Theorems.Thm_Formalism_GM_DetBound_gaussR_C
-- name    : Formalism.GM.DetBound.gaussR_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:51.610699+00:00
-- url     : https://prove2.me/theorems/989816e2-ec14-4137-b268-a5ba0fdb61ea
-- title:
--   Det Bound: gauss R C
-- statement:
--   The Det Bound construction uses the gauss R C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L46-L52

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

theorem Formalism.GM.DetBound.gaussR_C (ρ : NNReal) (a : K) : gaussR ρ (C a) = ‖a‖₊ := by sorry
