-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_QMinOp_qminorWordSum
-- name    : Formalism.FourierDecayAlt.P.CutMP.QMinOp.qminorWordSum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:22:34.278494+00:00
-- url     : https://prove2.me/theorems/60f5ac0f-a692-478f-ad60-ccc39faad393
-- title:
--   QMin Op: qminor Word Sum
-- statement:
--   The QMin Op construction uses the qminor Word Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJDHatQMinOp.lean#L15-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJDHatQMinOp.lean#L15-L46

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatQMinOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.QMinOp
open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.CutMP.QMinOp.qminorWordSum (k r t : ℕ) (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    ∃ L : List (ℂ × List (B.Mat k r)),
      (∀ cw ∈ L, (∀ X ∈ cw.2, B.unitLie k r X) ∧ cw.2.length ≤ t) ∧
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
        B.CkOn (t : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
          qminorOp (Q.EH k r) a b u f g = (L.map fun cw => cw.1 • B.Rw cw.2 f g).sum := by sorry
