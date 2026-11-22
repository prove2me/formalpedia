-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_nrm_pos
-- name    : Formalism.FourierDecayAlt.P.Mx4.nrm_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:52.942656+00:00
-- url     : https://prove2.me/theorems/8c74f41f-1bdb-4abf-8211-dd1bc85fa1b0
-- title:
--   Mx4: nrm pos
-- statement:
--   The Mx4 construction uses the nrm pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L343-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L343-L373

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}

theorem Formalism.FourierDecayAlt.P.Mx4.nrm_pos (P : Par) (hP : P.OK) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π π' : Ty P) (hU : Up P l π π') :
    0 < Nrm P l π := by sorry
