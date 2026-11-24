-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_INST_spr_upper
-- name    : Formalism.InvariantFactorPaths.INST.spr_upper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:21.611916+00:00
-- url     : https://prove2.me/theorems/5193b6dd-9b95-4d76-915d-169261cf6329
-- title:
--   INST: spr upper
-- statement:
--   The INST construction uses the spr upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/Spread.lean#L107-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/Spread.lean#L107-L112

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Spread
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

theorem Formalism.InvariantFactorPaths.INST.spr_upper (R : Type) [CommRing R] [IsDomain R] (r n : ℕ) (ν : Fin n → ℕ) (l : ℕ) (hl : ∀ t, ν t ≤ l)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ dualWeyl R r n ν) (m : Fin r × Fin n →₀ ℕ)
    (hm : m ∈ f.support) (a : Fin r) : rowDeg m a ≤ l := by sorry
