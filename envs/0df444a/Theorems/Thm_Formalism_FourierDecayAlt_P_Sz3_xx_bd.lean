-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_xx_bd
-- name    : Formalism.FourierDecayAlt.P.Sz3.xx_bd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:01.884805+00:00
-- url     : https://prove2.me/theorems/fb47315e-f848-4f8f-bab0-b8617c220ea0
-- title:
--   Sz3: xx bd
-- statement:
--   The Sz3 construction uses the xx bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L351-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L351-L371

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz3.xx_bd (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) (i i' : ℕ) (h : i < i') :
    |xx de i i'| ≤ 1 / 4 ∧ (xx de i i') ^ 2 ≤ 1 / 16 * (1 / (((i' - i : ℕ) : ℝ)) ^ 2) := by sorry
