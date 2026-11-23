-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_sq_lemma
-- name    : Formalism.FourierDecayAlt.P.Mx4.sq_lemma
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:21.610121+00:00
-- url     : https://prove2.me/theorems/2588c056-5e92-4551-b2ff-57ac01c7c1c0
-- title:
--   Mx4: sq lemma
-- statement:
--   The Mx4 construction uses the sq lemma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L564-L582
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L564-L582

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

theorem Formalism.FourierDecayAlt.P.Mx4.sq_lemma (a b a' b' d : ℝ) (h1 : a * (d - 1) = b' * (d + 1)) (h2 : a' * (d + 1) = b * (d - 1))
    (hd : 2 ≤ d ∨ d ≤ -2) :
    Real.sqrt a * Real.sqrt b * (d - 1) = Real.sqrt a' * Real.sqrt b' * (d + 1) ∧
      Real.sqrt a' * Real.sqrt a = Real.sqrt b' * Real.sqrt b := by sorry
