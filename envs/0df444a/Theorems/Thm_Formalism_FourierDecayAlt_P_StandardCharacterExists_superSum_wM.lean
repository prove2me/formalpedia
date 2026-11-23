-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_superSum_wM
-- name    : Formalism.FourierDecayAlt.P.StandardCharacterExists.superSum_wM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:41.529078+00:00
-- url     : https://prove2.me/theorems/4114bbc8-1e3a-4d26-a55b-3bf0117bf247
-- title:
--   Standard Character Exists: super Sum w M
-- statement:
--   The Standard Character Exists construction uses the super Sum w M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StandardCharacterExists.lean#L258-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StandardCharacterExists.lean#L258-L269

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

theorem Formalism.FourierDecayAlt.P.StandardCharacterExists.superSum_wM (m : ℕ) (X : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) (B ρ : Fin (m + 2) → ℂ) (σ : ℂ) :
    superSum (wMat (m + 3) * Mcoord 0 X B ρ σ) =
      ρ 1 + ∑ k ∈ Finset.Ico 0 (m + 1), ex (blk X B 0 0) k (k + 2) := by sorry
