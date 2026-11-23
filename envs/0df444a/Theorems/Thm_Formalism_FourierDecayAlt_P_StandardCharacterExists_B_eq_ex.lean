-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_B_eq_ex
-- name    : Formalism.FourierDecayAlt.P.StandardCharacterExists.B_eq_ex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:55.058064+00:00
-- url     : https://prove2.me/theorems/57e7bead-97b4-48bc-8635-86bd0fb5f610
-- title:
--   Standard Character Exists: B eq ex
-- statement:
--   The Standard Character Exists construction uses the B eq ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StandardCharacterExists.lean#L85-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StandardCharacterExists.lean#L85-L89

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

theorem Formalism.FourierDecayAlt.P.StandardCharacterExists.B_eq_ex {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B : Fin n → ℂ) (i : Fin n) :
    B i = ex (blk X B 0 0) i n := by sorry
