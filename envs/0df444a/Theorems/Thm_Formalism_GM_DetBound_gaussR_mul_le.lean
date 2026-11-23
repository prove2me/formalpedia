-- Prove2me | Theorems.Thm_Formalism_GM_DetBound_gaussR_mul_le
-- name    : Formalism.GM.DetBound.gaussR_mul_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:19.192286+00:00
-- url     : https://prove2.me/theorems/0d34e6eb-fdbc-4cb0-a3ed-e97dd810e625
-- title:
--   Det Bound: gauss R mul le
-- statement:
--   The Det Bound construction uses the gauss R mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L54-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L54-L63

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

theorem Formalism.GM.DetBound.gaussR_mul_le (ρ : NNReal) (P Q : K[X]) : gaussR ρ (P * Q) ≤ gaussR ρ P * gaussR ρ Q := by sorry
