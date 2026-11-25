-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_key
-- name    : Formalism.FourierDecayAlt.P.NFRadRedLocSec.key
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:30:30.757671+00:00
-- url     : https://prove2.me/theorems/92473b97-158c-5385-86a7-bd5f8a510033
-- title:
--   NFRad Red Loc Sec: key
-- statement:
--   The NFRad Red Loc Sec construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L294-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L294-L312

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedLocSec
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key

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

theorem Formalism.FourierDecayAlt.P.NFRadRedLocSec.key {z v : Fin (2 * r + k + 1) → ℂ} {ζ : ℂ} {T T' : ℝ} (hT : T ≠ 0) (hz : herm (Hpk k r) z z = -(T : ℂ))
    (hvz : herm (Hpk k r) v z = ζ) (hvv : herm (Hpk k r) v v = -(T' : ℂ)) :
    herm (Hpk k r) (v + (ζ / (T : ℂ)) • z) (v + (ζ / (T : ℂ)) • z) = (((Complex.normSq ζ - T * T') / T : ℝ) : ℂ) ∧
      herm (Hpk k r) z (v + (ζ / (T : ℂ)) • z) = 0 := by sorry
