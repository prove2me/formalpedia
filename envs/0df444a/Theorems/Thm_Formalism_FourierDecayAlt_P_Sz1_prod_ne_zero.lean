-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz1_prod_ne_zero
-- name    : Formalism.FourierDecayAlt.P.Sz1.prod_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:51.748638+00:00
-- url     : https://prove2.me/theorems/30e6ce43-a0bc-48f0-9044-abdefae89891
-- title:
--   Sz1: prod ne zero
-- statement:
--   The Sz1 construction uses the prod ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MassRatioFormula.lean#L49-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MassRatioFormula.lean#L49-L55

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz1
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz1.prod_ne_zero (k : ℕ) (q : ℝ) (hq : 1 < q) :
    ∏ i ∈ range k, (1 - (q ^ (i + 1))⁻¹) ≠ 0 := by sorry
