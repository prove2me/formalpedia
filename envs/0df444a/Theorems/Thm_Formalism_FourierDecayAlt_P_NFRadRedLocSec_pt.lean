-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_pt
-- name    : Formalism.FourierDecayAlt.P.NFRadRedLocSec.pt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:45:41.476684+00:00
-- url     : https://prove2.me/theorems/fef340f3-aa5d-454c-a37e-139046309934
-- title:
--   NFRad Red Loc Sec: pt
-- statement:
--   The NFRad Red Loc Sec construction uses the pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L408-L479
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L408-L479

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

theorem Formalism.FourierDecayAlt.P.NFRadRedLocSec.pt (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hsec : IsSection k r z z' μsec)
    {a₀ : Q.Mx k r} (ha₀ : a₀ ∈ UWset k r z) {g : Q.Mx k r} (hg : g ∈ Glev k r (Fin.last r))
    (hG : 0 < GGl k r z z' g) (hs : herm (Hpk k r) (u1 k r z z' μsec g) (u2 k r z z' a₀ g) ≠ 0) :
    af k r z z' μsec a₀ g ∈ UWset k r z ∧ bf k r z z' μsec a₀ g ∈ UWset k r z' ∧
      g = af k r z z' μsec a₀ g * muZ k r μsec (zetaL k r z z' (Fin.last r) g) * bf k r z z' μsec a₀ g := by sorry
