-- Prove2me | Theorems.Thm_Formalism_GM_DetBound_gaussR_le_iff
-- name    : Formalism.GM.DetBound.gaussR_le_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:15:25.658885+00:00
-- url     : https://prove2.me/theorems/7e4a102b-3710-4ac7-b74a-e44c6b38a851
-- title:
--   Det Bound: gauss R le iff
-- statement:
--   The Det Bound construction uses the gauss R le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L11-L20

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

theorem Formalism.GM.DetBound.gaussR_le_iff (ρ : NNReal) (P : K[X]) (b : NNReal) :
    gaussR ρ P ≤ b ↔ ∀ k, ‖P.coeff k‖₊ * ρ ^ k ≤ b := by sorry
