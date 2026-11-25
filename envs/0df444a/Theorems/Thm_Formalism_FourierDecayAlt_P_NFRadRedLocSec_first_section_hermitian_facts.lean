-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_first_section_hermitian_facts
-- name    : Formalism.FourierDecayAlt.P.NFRadRedLocSec.first_section_hermitian_facts
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:31:26.832715+00:00
-- url     : https://prove2.me/theorems/7d535042-e2e1-5ed2-885c-237426362b8e
-- title:
--   NFRad Red Loc Sec: first section hermitian facts
-- statement:
--   The NFRad Red Loc Sec construction uses the first section hermitian facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L344-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L344-L358

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
variable {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

theorem Formalism.FourierDecayAlt.P.NFRadRedLocSec.first_section_hermitian_facts (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hsec : IsSection k r z z' μsec)
    {g : Q.Mx k r} (hG : 0 < GGl k r z z' g) :
    herm (Hpk k r) (u1 k r z z' μsec g) (u1 k r z z' μsec g) = (qf k r z z' g : ℂ) ∧
      herm (Hpk k r) z (u1 k r z z' μsec g) = 0 ∧ inWb k r (u1 k r z z' μsec g) := by sorry
