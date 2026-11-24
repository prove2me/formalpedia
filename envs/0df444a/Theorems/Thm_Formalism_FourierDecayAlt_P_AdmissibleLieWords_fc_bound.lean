-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_fc_bound
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.fc_bound
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:13:49.226032+00:00
-- url     : https://prove2.me/theorems/ee0d55b3-ec53-4c6f-b5c2-b9ee9ed4dd0c
-- title:
--   Admissible Lie Words: fc bound
-- statement:
--   The Admissible Lie Words construction uses the fc bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BudgetClassEstimate.lean#L17-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BudgetClassEstimate.lean#L17-L67

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutoffIteratedFDerivBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetClassEstimate
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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.fc_bound (D : RealPlaceData k r Wp Wq) {χ₀ : ℝ → ℝ} (hχ : C6.IsCut0 χ₀) (de : ℝ) (L : Finset (Fin (r + 2)))
    {A₀ : ℝ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ∀ mm : ℕ, InCC A₀ mm F) (N : ℕ) :
    CkOn N (GV k r) (C6.cutAll D χ₀ de L F) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ W, admitted N W → ∀ g ∈ GV k r,
      ‖Dw W (C6.cutAll D χ₀ de L F) g‖ ≤ C * gN g ^ (-A₀ + (((2 * r + 2) * W.length : ℕ) : ℝ)) := by sorry
