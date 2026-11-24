-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_exp_hpart2_mem
-- name    : Formalism.FourierDecayAlt.Q.EabLie.exp_hpart2_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:41:39.553393+00:00
-- url     : https://prove2.me/theorems/8dcd89cf-57eb-4ea1-8bc0-e86b0350a18f
-- title:
--   Eab Lie: exp hpart2 mem
-- statement:
--   The Eab Lie construction uses the exp hpart2 mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DerivativePreservation/HasDerivAtExt.lean#L205-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DerivativePreservation/HasDerivAtExt.lean#L205-L208

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

theorem Formalism.FourierDecayAlt.Q.EabLie.exp_hpart2_mem (i : Fin (r + 1)) (p q : Fin (mdim k r i)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1))
      ∈ Glev k r i := by sorry
