-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_fdb
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.fdb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:48:58.331601+00:00
-- url     : https://prove2.me/theorems/30130a98-22d7-42b8-92ae-733b8704a8ec
-- title:
--   Admissible Lie Words: fdb
-- statement:
--   The Admissible Lie Words construction uses the fdb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplLen.lean#L167-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplLen.lean#L167-L242

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplLen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.fdb (ψ : Mat k r → F) (hψ : ContDiff ℝ ∞ ψ) (S : Set (Mat k r)) (K : Set F) (hK : ∀ g ∈ S, ψ g ∈ K)
    (Y : Mat k r → ℝ) (hY : ∀ g ∈ S, 1 ≤ Y g) (α β : ℕ) (M : ℝ) (n : ℕ)
    (H : ∀ w, admitted n w → w ≠ [] → ∀ g ∈ S, ‖Dw w ψ g‖ ≤ M * Y g ^ (α * w.length + β)) :
    ∀ m : ℕ, ∀ (E₁ : Type) [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] (Φ : F → E₁), ContDiff ℝ ∞ Φ →
      (∀ j : ℕ, ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ j Φ y‖ ≤ B) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ w, admitted n w → w.length ≤ m → ∀ g ∈ S,
        ‖Dw w (fun g => Φ (ψ g)) g‖ ≤ C * Y g ^ ((α + β) * w.length) := by sorry
