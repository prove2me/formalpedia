-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_up_mixed1
-- name    : Formalism.FourierDecayAlt.P.Mx4.up_mixed1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:21.058801+00:00
-- url     : https://prove2.me/theorems/f3525a30-bdff-4230-bc9b-6c74568736f4
-- title:
--   Mx4: up mixed1
-- statement:
--   The Mx4 construction uses the up mixed1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L477-L488
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L477-L488

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

theorem Formalism.FourierDecayAlt.P.Mx4.up_mixed1 (P : Par) (l j : ℕ) (hjl : j ≠ l) (π π1 π2 : Ty P) (h1 : Up P j π π1) (h2 : Up P l π2 π1) :
    ∃ π3, Up P l π3 π ∧ Up P j π3 π2 := by sorry
