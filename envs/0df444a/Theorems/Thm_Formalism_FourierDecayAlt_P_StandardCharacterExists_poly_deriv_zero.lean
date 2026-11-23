-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_poly_deriv_zero
-- name    : Formalism.FourierDecayAlt.P.StandardCharacterExists.poly_deriv_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:49.388935+00:00
-- url     : https://prove2.me/theorems/2ed2b1a1-1c4a-4644-af3c-911a6dae7de8
-- title:
--   Standard Character Exists: poly deriv zero
-- statement:
--   The Standard Character Exists construction uses the poly deriv zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StandardCharacterExists.lean#L177-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StandardCharacterExists.lean#L177-L179

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StandardCharacterExists

theorem Formalism.FourierDecayAlt.P.StandardCharacterExists.poly_deriv_zero (c : ℕ → ℂ) :
    HasDerivAt (fun t : ℂ => ∑ j ∈ Finset.range (0 + 1), c j * t ^ (0 - j)) 0 0 := by sorry
