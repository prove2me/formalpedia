-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_cdm_qrefl
-- name    : Formalism.FourierDecayAlt.P.NFRadRedLocSec.cdm_qrefl
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:46:43.581125+00:00
-- url     : https://prove2.me/theorems/8d169fa6-bfb6-4345-a2bf-ceeada9bb424
-- title:
--   NFRad Red Loc Sec: cdm qrefl
-- statement:
--   The NFRad Red Loc Sec construction uses the cdm qrefl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L185-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L185-L191

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

theorem Formalism.FourierDecayAlt.P.NFRadRedLocSec.cdm_qrefl (H : Matrix (Fin m) (Fin m) ℂ) {d : X → Fin m → ℂ} {c : X → ℂ} (hd : ContDiffOn ℝ n d s)
    (hc : ContDiffOn ℝ n c s) : ContDiffOn ℝ n (fun x => TwoByOneBlock.qrefl H (d x) (c x)) s := by sorry
