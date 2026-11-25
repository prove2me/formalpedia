-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_second_section_hermitian_facts
-- name    : Formalism.FourierDecayAlt.P.NFRadRedLocSec.second_section_hermitian_facts
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:32:41.633982+00:00
-- url     : https://prove2.me/theorems/9f829d4f-6391-4b56-8b7c-c7fff2b07fb3
-- title:
--   NFRad Red Loc Sec: second section hermitian facts
-- statement:
--   The NFRad Red Loc Sec construction uses the second section hermitian facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L377-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean#L377-L402

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

theorem Formalism.FourierDecayAlt.P.NFRadRedLocSec.second_section_hermitian_facts (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) {a₀ : Q.Mx k r}
    (ha₀ : a₀ ∈ UWset k r z) {g : Q.Mx k r} (hg : g ∈ Glev k r (Fin.last r)) :
    herm (Hpk k r) (u2 k r z z' a₀ g) (u2 k r z z' a₀ g) = (qf k r z z' g : ℂ) ∧
      herm (Hpk k r) z (u2 k r z z' a₀ g) = 0 ∧ inWb k r (u2 k r z z' a₀ g) := by sorry
