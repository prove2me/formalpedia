-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_up_square
-- name    : Formalism.FourierDecayAlt.P.Mx4.up_square
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:35.810518+00:00
-- url     : https://prove2.me/theorems/1c8936c7-0fb6-4e4b-b3a1-784deb2b2812
-- title:
--   Mx4: up square
-- statement:
--   The Mx4 construction uses the up square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L464-L475
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L464-L475

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

theorem Formalism.FourierDecayAlt.P.Mx4.up_square (P : Par) (l j : ℕ) (hjl : j ≠ l) (π π1 π2 : Ty P) (h1 : Up P l π π1) (h2 : Up P j π1 π2) :
    ∃ π3, Up P j π π3 ∧ Up P l π3 π2 := by sorry
