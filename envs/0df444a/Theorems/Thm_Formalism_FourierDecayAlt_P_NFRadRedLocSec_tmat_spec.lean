-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_tmat_spec
-- name    : Formalism.FourierDecayAlt.P.NFRadRedLocSec.tmat_spec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:57:06.739664+00:00
-- url     : https://prove2.me/theorems/d6e3b684-cecd-577c-aca1-fa23fdfdf6e2
-- title:
--   NFRad Red Loc Sec: tmat spec
-- statement:
--   The NFRad Red Loc Sec construction uses the tmat spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L103-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L103-L124

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
variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)
variable {H}

theorem Formalism.FourierDecayAlt.P.NFRadRedLocSec.tmat_spec (hH : Hᴴ = H) (a b : Fin m → ℂ) (q : ℝ) (hq : 0 < q)
    (ha : herm H a a = q) (hb : herm H b b = q) (hs : herm H a b ≠ 0) :
    tmat H a b q ∈ UH H ∧ tmat H a b q *ᵥ a = b ∧
    ∀ x, herm H x a = 0 → herm H x b = 0 → tmat H a b q *ᵥ x = x := by sorry
