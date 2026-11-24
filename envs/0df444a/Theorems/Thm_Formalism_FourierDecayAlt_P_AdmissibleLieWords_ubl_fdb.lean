-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ubl_fdb
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_fdb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:25:28.426851+00:00
-- url     : https://prove2.me/theorems/d516a98c-cf74-4fb5-880e-e24bc5b1e713
-- title:
--   Admissible Lie Words: ubl fdb
-- statement:
--   The Admissible Lie Words construction uses the ubl fdb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZinvBound.lean#L89-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZinvBound.lean#L89-L101

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

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_fdb {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ψ : Mat k r → F) (hψ : ContDiff ℝ ∞ ψ) (S : Set (Mat k r)) (hSG : S ⊆ GV k r) (K : Set F)
    (hK : ∀ g ∈ S, ψ g ∈ K) (α n : ℕ) (M : ℝ)
    (H : ∀ w, admitted n w → w ≠ [] → ∀ g ∈ GV k r, ‖Dw w ψ g‖ ≤ M * gN g ^ (α * w.length))
    (Φ : F → E) (hΦ : ContDiff ℝ ∞ Φ) (hB : ∀ j : ℕ, ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ j Φ y‖ ≤ B) :
    UBL (fun g => Φ (ψ g)) S n 0 α := by sorry
