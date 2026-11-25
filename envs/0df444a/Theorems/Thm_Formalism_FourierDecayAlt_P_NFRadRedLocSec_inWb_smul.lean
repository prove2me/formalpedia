-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_inWb_smul
-- name    : Formalism.FourierDecayAlt.P.NFRadRedLocSec.inWb_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:47:15.948797+00:00
-- url     : https://prove2.me/theorems/30556e37-bba7-499d-9db0-932fccec709e
-- title:
--   NFRad Red Loc Sec: in Wb smul
-- statement:
--   The NFRad Red Loc Sec construction uses the in Wb smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L290-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L290-L292

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedLocSec
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

theorem Formalism.FourierDecayAlt.P.NFRadRedLocSec.inWb_smul (c : ℂ) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : inWb k r (c • v) := by sorry
