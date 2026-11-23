-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_poly_zero
-- name    : Formalism.FourierDecayAlt.P.StandardCharacterExists.poly_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:40.928321+00:00
-- url     : https://prove2.me/theorems/e0e86d11-696d-47a5-bb8c-5679468ef23a
-- title:
--   Standard Character Exists: poly zero
-- statement:
--   The Standard Character Exists construction uses the poly zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StandardCharacterExists.lean#L169-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StandardCharacterExists.lean#L169-L175

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

theorem Formalism.FourierDecayAlt.P.StandardCharacterExists.poly_zero (m : ℕ) (c : ℕ → ℂ) : ∑ j ∈ Finset.range (m + 1), c j * (0 : ℂ) ^ (m - j) = c m := by sorry
