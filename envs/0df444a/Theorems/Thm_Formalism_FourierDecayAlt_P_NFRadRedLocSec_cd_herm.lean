-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_cd_herm
-- name    : Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_herm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:30:42.39843+00:00
-- url     : https://prove2.me/theorems/624b7dbc-8a82-5bd9-816a-4992d9cb6d2e
-- title:
--   NFRad Red Loc Sec: cd herm
-- statement:
--   The NFRad Red Loc Sec construction uses the cd herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L176-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L176-L183

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

theorem Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_herm (H : Matrix (Fin m) (Fin m) ℂ) {A B : X → Fin m → ℂ} (hA : ContDiffOn ℝ n A s)
    (hB : ContDiffOn ℝ n B s) : ContDiffOn ℝ n (fun x => herm H (A x) (B x)) s := by sorry
