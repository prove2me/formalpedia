-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_NF_bd
-- name    : Formalism.FourierDecayAlt.P.Sz3.NF_bd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:47.638996+00:00
-- url     : https://prove2.me/theorems/65d13a33-a7f7-476d-8b46-bd86b0ed485e
-- title:
--   Sz3: NF bd
-- statement:
--   The Sz3 construction uses the NF bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L307-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L307-L344

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

theorem Formalism.FourierDecayAlt.P.Sz3.NF_bd (J : ℕ) (hJ : 1 ≤ J) (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) :
    |NF J de| ≤ 7 / 10 * (J : ℝ) + 1 := by sorry
