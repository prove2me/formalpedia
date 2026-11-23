-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_corner
-- name    : Formalism.FourierDecayAlt.P.Mx4.corner
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:17.834276+00:00
-- url     : https://prove2.me/theorems/68221ab2-42ed-418f-b76c-78bdd8bf0bed
-- title:
--   Mx4: corner
-- statement:
--   The Mx4 construction uses the corner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L584-L596
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L584-L596

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

theorem Formalism.FourierDecayAlt.P.Mx4.corner (P : Par) (hP : P.OK) (l j : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l)
    (π πl πj : Ty P) (h1 : Up P l π πl) (h2 : Up P j π πj) :
    Real.sqrt (Nrm P j πl) * Real.sqrt (Nrm P l π) * (rho P π j - rho P π l - 1) =
      Real.sqrt (Nrm P l πj) * Real.sqrt (Nrm P j π) * (rho P π j - rho P π l + 1) ∧
    Real.sqrt (Nrm P l πj) * Real.sqrt (Nrm P j πl) = Real.sqrt (Nrm P j π) * Real.sqrt (Nrm P l π) := by sorry
