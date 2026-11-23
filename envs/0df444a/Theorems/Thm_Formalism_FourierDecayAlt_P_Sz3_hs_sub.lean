-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_hs_sub
-- name    : Formalism.FourierDecayAlt.P.Sz3.hs_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:59.235934+00:00
-- url     : https://prove2.me/theorems/0ef4404e-42e9-49fc-a8c8-331b16ab36ab
-- title:
--   Sz3: hs sub
-- statement:
--   The Sz3 construction uses the hs sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L261-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L261-L264

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

theorem Formalism.FourierDecayAlt.P.Sz3.hs_sub (p J : ℕ) (h : p ≤ J) : ∑ d ∈ Ioc p J, 1 / (d : ℝ) = hs J - hs p := by sorry
