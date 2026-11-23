-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_wM_zero_last
-- name    : Formalism.FourierDecayAlt.P.StandardCharacterExists.wM_zero_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:40.024465+00:00
-- url     : https://prove2.me/theorems/6f04f11e-3c0c-4960-9cb5-6f88e8158a42
-- title:
--   Standard Character Exists: w M zero last
-- statement:
--   The Standard Character Exists construction uses the w M zero last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StandardCharacterExists.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StandardCharacterExists.lean#L54-L56

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

theorem Formalism.FourierDecayAlt.P.StandardCharacterExists.wM_zero_last {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) :
    (wMat (n + 1) * Mcoord 0 X B ρ σ) 0 (Fin.last n) = σ := by sorry
