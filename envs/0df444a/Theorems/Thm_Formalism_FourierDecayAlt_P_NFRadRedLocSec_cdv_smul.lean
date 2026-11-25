-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_cdv_smul
-- name    : Formalism.FourierDecayAlt.P.NFRadRedLocSec.cdv_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:31:08.025393+00:00
-- url     : https://prove2.me/theorems/9551aeac-bee6-5590-98d1-5ac67708fa0e
-- title:
--   NFRad Red Loc Sec: cdv smul
-- statement:
--   The NFRad Red Loc Sec construction uses the cdv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L170-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L170-L174

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
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {s : Set X} {m : ℕ}

theorem Formalism.FourierDecayAlt.P.NFRadRedLocSec.cdv_smul {c : X → ℂ} {v : X → Fin m → ℂ} (hc : ContDiffOn ℝ n c s) (hv : ContDiffOn ℝ n v s) :
    ContDiffOn ℝ n (fun x => c x • v x) s := by sorry
