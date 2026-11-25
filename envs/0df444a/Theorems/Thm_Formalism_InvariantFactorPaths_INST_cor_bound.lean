-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_INST_cor_bound
-- name    : Formalism.InvariantFactorPaths.INST.cor_bound
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:59:57.49023+00:00
-- url     : https://prove2.me/theorems/ddbc9d0d-bea2-415c-9ce1-7725bb7d70f1
-- title:
--   INST: cor bound
-- statement:
--   The INST construction uses the cor bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/SwappedHighestWeightNeZero.lean#L32-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/SwappedHighestWeightNeZero.lean#L32-L46

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_SwappedHighestWeightNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.InvariantFactorPaths.PW
variable {p : ℕ} [Fact p.Prime] {r n : ℕ}

theorem Formalism.InvariantFactorPaths.INST.cor_bound (hw : SwpWt) (ν : Fin n → ℕ) (l : ℕ) (hS : Spread ℚ_[p] r n ν l) :
    ∀ (μ μ' : Fin r → ℤ) (x y : MvPolynomial (Fin n × Fin r) ℚ_[p]), x ≠ 0 → y ≠ 0 →
      x ∈ swappedDualWeyl p r n ν → y ∈ swappedDualWeyl p r n ν → (GR p r ν).IsWt μ x → (GR p r ν).IsWt μ' y →
      ∀ c, |μ' c - μ c| ≤ (l : ℤ) := by sorry
