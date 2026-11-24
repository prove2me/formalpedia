-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresLie_hasDerivAt_ext
-- name    : Formalism.FourierDecayAlt.Q.TPresLie.hasDerivAt_ext
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:58:40.788034+00:00
-- url     : https://prove2.me/theorems/c9ba4046-3050-4ec1-b288-e9b4f3a07883
-- title:
--   TPres Lie: has Deriv At ext
-- statement:
--   The TPres Lie construction uses the has Deriv At ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/HasDerivAtExt.lean#L187-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/HasDerivAtExt.lean#L187-L207

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_HasDerivAtExt
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.Q.TPresLie.hasDerivAt_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (i : Fin (r + 1)) (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    (f F : Mx k r → E) (U : Set (Mx k r)) (g : Mx k r) (hU : IsOpen U) (hg : g ∈ U)
    (hgG : g ∈ Glev k r i) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ x ∈ U, x ∈ Glev k r i → f x = F x) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by sorry
