-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_norm_cof_rest_le
-- name    : Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.norm_cof_rest_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:35.98709+00:00
-- url     : https://prove2.me/theorems/864d7062-afc6-47bc-843a-8e235c5c0e68
-- title:
--   Whittaker Vanishing Implies Zero: norm cof rest le
-- statement:
--   The Whittaker Vanishing Implies Zero construction uses the norm cof rest le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L335-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L335-L355

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

theorem Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.norm_cof_rest_le {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} {B : Fin (m + 1) → ℂ}
    {t : ℂ} {L : ℝ} (hL : 1 ≤ L) (ht : ‖t‖ ≤ 1) (hX : ∀ i j, ‖X i j‖ ≤ L) (hB : ∀ i, ‖B i‖ ≤ L) :
    ‖∑ j ∈ Finset.range m, ((-X) ^ j *ᵥ B) 0 * t ^ (m - j)‖ ≤
      ((m : ℝ) * ((m : ℝ) + 1) ^ m) * (L ^ (m + 1) * ‖t‖) := by sorry
