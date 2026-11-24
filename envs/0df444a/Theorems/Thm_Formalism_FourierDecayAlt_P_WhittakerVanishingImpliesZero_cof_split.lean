-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_cof_split
-- name    : Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.cof_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:49:55.016885+00:00
-- url     : https://prove2.me/theorems/b6b77a7b-a57f-4844-b9ca-e7da82086aab
-- title:
--   Whittaker Vanishing Implies Zero: cof split
-- statement:
--   The Whittaker Vanishing Implies Zero construction uses the cof split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L328-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L328-L333

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G6

theorem Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.cof_split {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} (hS : IsStrictUpper X)
    (B : Fin (m + 1) → ℂ) (t : ℂ) :
    Cof X B t = (∑ j ∈ Finset.range m, ((-X) ^ j *ᵥ B) 0 * t ^ (m - j)) + (-1) ^ m * ∏ k, xOf X B k := by sorry
