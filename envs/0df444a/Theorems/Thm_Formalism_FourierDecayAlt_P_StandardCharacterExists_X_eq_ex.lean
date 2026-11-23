-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_X_eq_ex
-- name    : Formalism.FourierDecayAlt.P.StandardCharacterExists.X_eq_ex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:32.925567+00:00
-- url     : https://prove2.me/theorems/e9d04ab2-1247-4e37-bf07-464dd1575be2
-- title:
--   Standard Character Exists: X eq ex
-- statement:
--   The Standard Character Exists construction uses the X eq ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StandardCharacterExists.lean#L79-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StandardCharacterExists.lean#L79-L83

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

theorem Formalism.FourierDecayAlt.P.StandardCharacterExists.X_eq_ex {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B : Fin n → ℂ) (i k : Fin n) :
    X i k = ex (blk X B 0 0) i k := by sorry
