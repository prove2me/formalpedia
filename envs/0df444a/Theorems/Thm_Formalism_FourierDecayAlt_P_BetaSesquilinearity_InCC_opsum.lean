-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_InCC_opsum
-- name    : Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_opsum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:27:50.4358+00:00
-- url     : https://prove2.me/theorems/d55fa5e5-cabe-42ef-b507-a80065128d24
-- title:
--   Beta Sesquilinearity: In CC opsum
-- statement:
--   The Beta Sesquilinearity construction uses the In CC opsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaSesquilinearity.lean#L926-L933
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaSesquilinearity.lean#L926-L933

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

theorem Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_opsum {ι : Type*} {A : ℝ} {m : ℕ} (Θ : List ι) (φ : ι → Mat k r → E)
    (h : ∀ T ∈ Θ, InCC A m (φ T)) : InCC A m (fun g => (Θ.map fun T => φ T g).sum) := by sorry
