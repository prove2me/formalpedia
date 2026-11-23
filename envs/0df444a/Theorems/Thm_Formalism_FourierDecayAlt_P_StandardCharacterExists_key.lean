-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_key
-- name    : Formalism.FourierDecayAlt.P.StandardCharacterExists.key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:09:48.410597+00:00
-- url     : https://prove2.me/theorems/76bd197c-34c8-4337-9299-212ba52ba596
-- title:
--   Standard Character Exists: key
-- statement:
--   The Standard Character Exists construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StandardCharacterExists.lean#L96-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StandardCharacterExists.lean#L96-L167

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

theorem Formalism.FourierDecayAlt.P.StandardCharacterExists.key (m : ℕ) (z : ℂ) (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ)
    (hX : IsStrictUpper X) (hx : ∀ k, xOf X B k = z) (j : ℕ) :
    (∀ i : Fin (m + 1), m < (i : ℕ) + j → ((-X) ^ j *ᵥ B) i = 0) ∧
    (∀ i : Fin (m + 1), (i : ℕ) + j = m → ((-X) ^ j *ᵥ B) i = (-z) ^ j * z) ∧
    (∀ i : Fin (m + 1), (i : ℕ) + j + 1 = m →
      ((-X) ^ j *ᵥ B) i = (-z) ^ j * ∑ k ∈ Finset.Ico (i : ℕ) m, ex (blk X B 0 0) k (k + 2)) := by sorry
