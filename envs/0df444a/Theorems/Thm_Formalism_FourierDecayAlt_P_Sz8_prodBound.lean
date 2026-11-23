-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz8_prodBound
-- name    : Formalism.FourierDecayAlt.P.Sz8.prodBound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:37:05.608853+00:00
-- url     : https://prove2.me/theorems/64dbc28a-b3fd-4092-80a4-a7939d4ab6fb
-- title:
--   Sz8: prod Bound
-- statement:
--   The Sz8 construction uses the prod Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmRingIdempotentUnitRatioIdentity.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmRingIdempotentUnitRatioIdentity.lean#L9-L17

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.Sz Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.Sz8

theorem Formalism.FourierDecayAlt.P.Sz8.prodBound {ι : Type} [Fintype ι] (F t : ι → ℝ) (K Ct : ℝ) (hK : 0 ≤ K)
    (hF : ∀ w, 0 ≤ F w ∧ F w ≤ K * t w) (ht : ∏ w, t w ≤ Ct) :
    ∏ w, F w ≤ Ct * K ^ Fintype.card ι := by sorry
