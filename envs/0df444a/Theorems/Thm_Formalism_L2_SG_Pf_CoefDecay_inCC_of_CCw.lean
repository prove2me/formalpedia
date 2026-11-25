-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_CoefDecay_inCC_of_CCw
-- name    : Formalism.L2.SG.Pf.CoefDecay.inCC_of_CCw
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:48:58.018183+00:00
-- url     : https://prove2.me/theorems/a5c0c9dc-2359-5557-adb6-65d7beaa3260
-- title:
--   Coef Decay: in CC of CCw
-- statement:
--   The Coef Decay construction uses the in CC of CCw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/CoefDecayA.lean#L36-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/CoefDecayA.lean#L36-L95

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

theorem Formalism.L2.SG.Pf.CoefDecay.inCC_of_CCw {A : ℝ} {F : B.Mat k r → E} (hF : CCw k r A F) (m : ℕ) :
    B.InCC (k := k) (r := r) A m F := by sorry
