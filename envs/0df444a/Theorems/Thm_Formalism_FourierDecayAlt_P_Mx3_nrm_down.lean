-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_nrm_down
-- name    : Formalism.FourierDecayAlt.P.Mx3.nrm_down
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:06.463592+00:00
-- url     : https://prove2.me/theorems/a3c0652b-6267-4d04-b5a4-8ec40a981392
-- title:
--   Mx3: nrm down
-- statement:
--   The Mx3 construction uses the nrm down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InterlaceSignTwo.lean#L187-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InterlaceSignTwo.lean#L187-L206

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx3

theorem Formalism.FourierDecayAlt.P.Mx3.nrm_down (P : Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π π' : Ty P) (hU : Up P l π π') :
    NrmDown P l π' = Nrm P l π := by sorry
