-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_map_mul_vol
-- name    : Formalism.FourierDecayAlt.P.StandardCharacterExists.map_mul_vol
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:40.937017+00:00
-- url     : https://prove2.me/theorems/46ad149b-a6f4-4f9c-b1b0-a20cb7909a70
-- title:
--   Standard Character Exists: map mul vol
-- statement:
--   The Standard Character Exists construction uses the map mul vol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StandardCharacterExists.lean#L197-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StandardCharacterExists.lean#L197-L207

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

theorem Formalism.FourierDecayAlt.P.StandardCharacterExists.map_mul_vol (α : ℂ) (hα : α ≠ 0) :
    Measure.map (fun ρ : ℂ => α * ρ) (volume : Measure ℂ) = ENNReal.ofReal ((‖α‖ ^ 2)⁻¹) • volume := by sorry
