-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_exp_mem_glev
-- name    : Formalism.FourierDecayAlt.Q.EabLie.exp_mem_glev
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:24:03.755892+00:00
-- url     : https://prove2.me/theorems/5e98707c-f2d3-4c7d-8f36-f030625853bf
-- title:
--   Eab Lie: exp mem glev
-- statement:
--   The Eab Lie construction uses the exp mem glev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DerivativePreservation/HasDerivAtExt.lean#L131-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DerivativePreservation/HasDerivAtExt.lean#L131-L136

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_HasDerivAtExt
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabLie
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.Q.EabLie.exp_mem_glev (i : Fin (r + 1)) (X : Mx k r) (hX : Xᴴ = -(Hpk k r * X * Hpk k r))
    (hc : ∀ a : Fin r, a.val < i.val → ∀ x, X x (eI k r a) = 0 ∧ X x (esI k r a) = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by sorry
