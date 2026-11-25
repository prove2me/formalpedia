-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_herm_out
-- name    : Formalism.FourierDecayAlt.P.NFRadRedLocSec.herm_out
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:30:28.547371+00:00
-- url     : https://prove2.me/theorems/9abd1b14-7c53-5db2-9bd6-759caaada55f
-- title:
--   NFRad Red Loc Sec: herm out
-- statement:
--   The NFRad Red Loc Sec construction uses the herm out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L257-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L257-L262

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

theorem Formalism.FourierDecayAlt.P.NFRadRedLocSec.herm_out {d : Fin (2 * r + k + 1) → ℂ} (hd : inWb k r d) {i : Fin (2 * r + k + 1)}
    (hi : ¬ TwoByOneBlock.mid k r i) : herm (Hpk k r) (bvec i) d = 0 := by sorry
