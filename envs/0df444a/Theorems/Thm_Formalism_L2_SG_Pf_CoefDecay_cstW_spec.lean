-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_CoefDecay_cstW_spec
-- name    : Formalism.L2.SG.Pf.CoefDecay.cstW_spec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:55:32.275064+00:00
-- url     : https://prove2.me/theorems/aaccc99b-b4b3-4a66-8627-35a96957a427
-- title:
--   Coef Decay: cst W spec
-- statement:
--   The Coef Decay construction uses the cst W spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/CoefDecayA.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/CoefDecayA.lean#L24-L29

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_SmoothClassInFiniteOrder
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_CoefDecayA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.CoefDecay
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt PI.ComplexConjugateDerivative
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.L2.SG.Pf.CoefDecay.cstW_spec {A : ℝ} {F : B.Mat k r → E} (hF : CCw k r A F) (u v : List (B.Mat k r))
    (hu : ∀ X ∈ u, B.unitLie k r X) (hv : ∀ X ∈ v, B.unitLie k r X) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    B.gN g ^ A * ‖B.dLR u v F g‖ ≤ cstW hF u v := by sorry
