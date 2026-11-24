-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_leib_bound
-- name    : Formalism.FourierDecayAlt.P.BetaSesquilinearity.leib_bound
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:24:53.177948+00:00
-- url     : https://prove2.me/theorems/5f059188-4408-4d7c-a77d-4759b88ae91f
-- title:
--   Beta Sesquilinearity: leib bound
-- statement:
--   The Beta Sesquilinearity construction uses the leib bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaSesquilinearity.lean#L451-L489
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaSesquilinearity.lean#L451-L489

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {O UU : Set (Mat k r)} {a : Mat k r → (E →L[ℂ] E')} {Φ : Mat k r → E}

theorem Formalism.FourierDecayAlt.P.BetaSesquilinearity.leib_bound (hO : IsOpen O) (hcov : ∀ g ∈ GV k r, g ∈ O ∨ g ∈ UU) (g : Mat k r) (hg : g ∈ GV k r)
    (M : ℝ) (w : List (Bool × Mat k r)) :
    ∀ (a : Mat k r → (E →L[ℂ] E')) (Φ : Mat k r → E), (∀ x ∈ w, inLie k r x.2) → Pr O UU w.length a Φ →
      (∀ w₁ w₂ : List (Bool × Mat k r), w₁.Sublist w → w₂.Sublist w → w₁.length + w₂.length = w.length →
        ‖Dw w₁ a g‖ * ‖Dw w₂ Φ g‖ ≤ M) →
      ‖Dw w (ap a Φ) g‖ ≤ 2 ^ w.length * M := by sorry
