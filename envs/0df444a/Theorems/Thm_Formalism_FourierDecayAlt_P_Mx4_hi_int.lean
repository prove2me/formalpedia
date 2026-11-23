-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_hi_int
-- name    : Formalism.FourierDecayAlt.P.Mx4.hi_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:14.948872+00:00
-- url     : https://prove2.me/theorems/6f106fa5-b3b8-4b8c-8d3c-f6b47fbb4577
-- title:
--   Mx4: hi int
-- statement:
--   The Mx4 construction uses the hi int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L292-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L292-L299

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

theorem Formalism.FourierDecayAlt.P.Mx4.hi_int (P : Par) (hP : P.OK) (i : ℕ) (hi : i ∈ Icc 1 (P.k - 1)) : ∃ n : ℤ, P.hi i - P.u 1 + 1 / 2 = n := by sorry
