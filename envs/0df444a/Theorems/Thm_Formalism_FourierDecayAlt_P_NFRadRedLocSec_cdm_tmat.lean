-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_cdm_tmat
-- name    : Formalism.FourierDecayAlt.P.NFRadRedLocSec.cdm_tmat
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:48:25.142386+00:00
-- url     : https://prove2.me/theorems/8616ae2f-ba56-4ab9-bc46-0dc44f4e3e30
-- title:
--   NFRad Red Loc Sec: cdm tmat
-- statement:
--   The NFRad Red Loc Sec construction uses the cdm tmat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L193-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L193-L210

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

theorem Formalism.FourierDecayAlt.P.NFRadRedLocSec.cdm_tmat (H : Matrix (Fin m) (Fin m) ℂ) {A B : X → Fin m → ℂ} {Q : X → ℝ} (hA : ContDiffOn ℝ n A s)
    (hB : ContDiffOn ℝ n B s) (hQ : ContDiffOn ℝ n Q s) (hs : ∀ x ∈ s, herm H (A x) (B x) ≠ 0)
    (hq : ∀ x ∈ s, 0 < Q x) : ContDiffOn ℝ n (fun x => tmat H (A x) (B x) (Q x)) s := by sorry
