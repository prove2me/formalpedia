-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_prodBound
-- name    : Formalism.FourierDecayAlt.P.BetaSesquilinearity.prodBound
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:32:29.193012+00:00
-- url     : https://prove2.me/theorems/f23a7f78-7c1c-4472-a4fd-fdf16071b6d5
-- title:
--   Beta Sesquilinearity: prod Bound
-- statement:
--   The Beta Sesquilinearity construction uses the prod Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaSesquilinearity.lean#L700-L743
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaSesquilinearity.lean#L700-L743

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

theorem Formalism.FourierDecayAlt.P.BetaSesquilinearity.prodBound {O UU : Set (Mat k r)} (hO : IsOpen O) (hcov : ∀ g ∈ GV k r, g ∈ O ∨ g ∈ UU)
    {A d : ℝ} {m : ℕ} {a : Mat k r → (E →L[ℂ] E')} {Φ : Mat k r → E} {C c : ℝ}
    (ha : CkOn m UU a)
    (hab : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ GV k r, g ∉ O → ‖dLR u v a g‖ ≤ C * gN g ^ d)
    (hΦ : CCle (A + d) m Φ c) (hz : ∀ g ∈ GV k r, g ∈ O → Φ g = 0) :
    CCle A m (ap a Φ) (2 ^ m * (|C| * |c|)) := by sorry
