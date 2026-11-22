-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_gap
-- name    : Formalism.FourierDecayAlt.P.Mx4.gap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:06:03.374029+00:00
-- url     : https://prove2.me/theorems/054cfdd5-b84b-4f29-b2a9-65fb45470810
-- title:
--   Mx4: gap
-- statement:
--   The Mx4 construction uses the gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L543-L562
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L543-L562

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

theorem Formalism.FourierDecayAlt.P.Mx4.gap (P : Par) (hP : P.OK) (l j : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l)
    (π πl πj : Ty P) (h1 : Up P l π πl) (h2 : Up P j π πj) :
    2 ≤ rho P π j - rho P π l ∨ rho P π j - rho P π l ≤ -2 := by sorry
