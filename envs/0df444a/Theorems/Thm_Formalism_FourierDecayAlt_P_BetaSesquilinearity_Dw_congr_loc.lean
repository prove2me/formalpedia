-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dw_congr_loc
-- name    : Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_congr_loc
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:24:47.291797+00:00
-- url     : https://prove2.me/theorems/e65485b1-ff52-4838-969e-c16e1ade644f
-- title:
--   Beta Sesquilinearity: Dw congr loc
-- statement:
--   The Beta Sesquilinearity construction uses the Dw congr loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaSesquilinearity.lean#L152-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaSesquilinearity.lean#L152-L159

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

theorem Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_congr_loc {w : List (Bool × Mat k r)} (hw : ∀ x ∈ w, inLie k r x.2) {O : Set (Mat k r)}
    (hO : IsOpen O) {f f₂ : Mat k r → E} (h : ∀ g ∈ GV k r, g ∈ O → f g = f₂ g) :
    ∀ g ∈ GV k r, g ∈ O → Dw w f g = Dw w f₂ g := by sorry
