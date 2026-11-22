-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_coord_ne
-- name    : Formalism.FourierDecayAlt.P.Mx4.coord_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:02.616363+00:00
-- url     : https://prove2.me/theorems/1dac4f88-5a01-48ab-8879-e26c1d72ed07
-- title:
--   Mx4: coord ne
-- statement:
--   The Mx4 construction uses the coord ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L61-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L61-L62

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

theorem Formalism.FourierDecayAlt.P.Mx4.coord_ne (r : ℕ) (v : Var r) : coord v ≠ 0 := by sorry
