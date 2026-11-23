-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_lo_int
-- name    : Formalism.FourierDecayAlt.P.Mx4.lo_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:06.263047+00:00
-- url     : https://prove2.me/theorems/a0b9e050-da37-4a80-8f7d-0cbe73ea5bb8
-- title:
--   Mx4: lo int
-- statement:
--   The Mx4 construction uses the lo int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L283-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L283-L290

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

theorem Formalism.FourierDecayAlt.P.Mx4.lo_int (P : Par) (hP : P.OK) (i : ℕ) (hi : i ∈ Icc 1 (P.k - 1)) : ∃ n : ℤ, P.lo i - P.u 1 - 1 / 2 = n := by sorry
