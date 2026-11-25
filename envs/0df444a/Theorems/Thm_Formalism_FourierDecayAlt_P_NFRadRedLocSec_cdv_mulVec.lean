-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_cdv_mulVec
-- name    : Formalism.FourierDecayAlt.P.NFRadRedLocSec.cdv_mulVec
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:47:36.689544+00:00
-- url     : https://prove2.me/theorems/ae030a2b-47d4-562f-a6d5-f5a4bf9decd5
-- title:
--   NFRad Red Loc Sec: cdv mul Vec
-- statement:
--   The NFRad Red Loc Sec construction uses the cdv mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L164-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L164-L168

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

theorem Formalism.FourierDecayAlt.P.NFRadRedLocSec.cdv_mulVec {F : X → Matrix (Fin m) (Fin m) ℂ} (hF : ContDiffOn ℝ n F s) (v : Fin m → ℂ) :
    ContDiffOn ℝ n (fun x => F x *ᵥ v) s := by sorry
