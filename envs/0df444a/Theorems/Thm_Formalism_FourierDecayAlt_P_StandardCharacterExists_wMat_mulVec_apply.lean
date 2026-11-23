-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_wMat_mulVec_apply
-- name    : Formalism.FourierDecayAlt.P.StandardCharacterExists.wMat_mulVec_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:36.600208+00:00
-- url     : https://prove2.me/theorems/d71667ad-eda3-43c7-8c8e-642a9f9b027c
-- title:
--   Standard Character Exists: w Mat mul Vec apply
-- statement:
--   The Standard Character Exists construction uses the w Mat mul Vec apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StandardCharacterExists.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StandardCharacterExists.lean#L39-L40

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

theorem Formalism.FourierDecayAlt.P.StandardCharacterExists.wMat_mulVec_apply {d : ℕ} (b : Fin d → ℂ) (i : Fin d) : (wMat d *ᵥ b) i = b i.rev := by sorry
