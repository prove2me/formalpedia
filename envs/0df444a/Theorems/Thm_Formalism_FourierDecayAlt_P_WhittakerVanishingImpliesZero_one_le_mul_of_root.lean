-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_one_le_mul_of_root
-- name    : Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.one_le_mul_of_root
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:51.112783+00:00
-- url     : https://prove2.me/theorems/332e132d-4c6c-42a0-b689-3f19edf26193
-- title:
--   Whittaker Vanishing Implies Zero: one le mul of root
-- statement:
--   The Whittaker Vanishing Implies Zero construction uses the one le mul of root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L150-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L150-L167

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
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.one_le_mul_of_root {s : ℕ} {ζ : ℂ} (hs : 0 < s) (h : ζ ^ s = 1) (hne : ζ ≠ 1) :
    1 ≤ (s : ℝ) * ‖ζ - 1‖ := by sorry
