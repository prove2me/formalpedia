-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_INST_dsc_split
-- name    : Formalism.InvariantFactorPaths.INST.dsc_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:47.408485+00:00
-- url     : https://prove2.me/theorems/35fefd75-b41c-45d6-948a-593c72d4a861
-- title:
--   INST: dsc split
-- statement:
--   The INST construction uses the dsc split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/Descent.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/Descent.lean#L30-L35

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Descent
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
open Formalism.GradedWeylDivisibility

theorem Formalism.InvariantFactorPaths.INST.dsc_split (p : ℕ) [hp : Fact p.Prime] (N : ℤ) (hN : N ≠ 0) :
    ∃ (k : ℕ) (c : ℤ), N = (p : ℤ) ^ k * c ∧ ¬ (p : ℤ) ∣ c := by sorry
