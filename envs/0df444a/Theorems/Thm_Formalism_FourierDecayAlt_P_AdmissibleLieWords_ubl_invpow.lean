-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ubl_invpow
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_invpow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:26:06.794085+00:00
-- url     : https://prove2.me/theorems/99135686-b6e4-4b03-9bcf-e9497614dadd
-- title:
--   Admissible Lie Words: ubl invpow
-- statement:
--   The Admissible Lie Words construction uses the ubl invpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZinvBound.lean#L174-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZinvBound.lean#L174-L186

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZinvBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_invpow {d : ℕ} {P : Mat k r → ℂ} (hP : U.IsPolyDeg d P) {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {c : ℝ} (hc : 0 < c) (hS : ∀ g ∈ S, c ≤ Complex.normSq (P g)) (m n : ℕ) :
    UBL (fun g => (P g)⁻¹ ^ m) S n 0 d := by sorry
