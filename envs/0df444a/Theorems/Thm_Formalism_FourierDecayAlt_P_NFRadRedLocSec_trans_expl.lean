-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_trans_expl
-- name    : Formalism.FourierDecayAlt.P.NFRadRedLocSec.trans_expl
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:49:21.862483+00:00
-- url     : https://prove2.me/theorems/ce760e6e-c01b-4d08-ae3b-c0cd8824eff7
-- title:
--   NFRad Red Loc Sec: trans expl
-- statement:
--   The NFRad Red Loc Sec construction uses the trans expl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L26-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L26-L101

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

theorem Formalism.FourierDecayAlt.P.NFRadRedLocSec.trans_expl (hH : Hᴴ = H) (a b : Fin m → ℂ) (q : ℝ) (hq : q ≠ 0)
    (ha : herm H a a = q) (hb : herm H b b = q) (θ : ℂ) (t : ℝ) (hθ : θ * star θ = 1)
    (ht : star θ * herm H a b = t) (hqt : q * t ≤ 0) :
    TwoByOneBlock.qrefl H b ((star θ - 1) / q) * TwoByOneBlock.qrefl H (a + (-θ) • b) (-1 / ((q : ℂ) - t)) ∈ UH H ∧
    (TwoByOneBlock.qrefl H b ((star θ - 1) / q) * TwoByOneBlock.qrefl H (a + (-θ) • b) (-1 / ((q : ℂ) - t))) *ᵥ a = b ∧
    ∀ x, herm H x a = 0 → herm H x b = 0 →
      (TwoByOneBlock.qrefl H b ((star θ - 1) / q) * TwoByOneBlock.qrefl H (a + (-θ) • b) (-1 / ((q : ℂ) - t))) *ᵥ x = x := by sorry
