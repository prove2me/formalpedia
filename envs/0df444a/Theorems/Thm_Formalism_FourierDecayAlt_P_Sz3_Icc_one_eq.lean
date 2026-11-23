-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_Icc_one_eq
-- name    : Formalism.FourierDecayAlt.P.Sz3.Icc_one_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:08.664718+00:00
-- url     : https://prove2.me/theorems/a11416cb-6875-400d-9a18-7d5387173c55
-- title:
--   Sz3: Icc one eq
-- statement:
--   The Sz3 construction uses the Icc one eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L283-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L283-L284

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

theorem Formalism.FourierDecayAlt.P.Sz3.Icc_one_eq (n : ℕ) : Icc 1 n = Ioc 0 n := by sorry
