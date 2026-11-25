-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_inv_fix
-- name    : Formalism.FourierDecayAlt.P.NFRadRedLocSec.inv_fix
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:30:45.652221+00:00
-- url     : https://prove2.me/theorems/bf9670a8-00b0-56e8-98cc-85db70ff240c
-- title:
--   NFRad Red Loc Sec: inv fix
-- statement:
--   The NFRad Red Loc Sec construction uses the inv fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L333-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L333-L335

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedLocSec
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_inv_fix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFRadRedLocSec
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.NFRadRedLocSec.inv_fix {X : Q.Mx k r} (hu : IsUnit X.det) {v w : Fin (2 * r + k + 1) → ℂ} (h : X *ᵥ v = w) :
    X⁻¹ *ᵥ w = v := by sorry
