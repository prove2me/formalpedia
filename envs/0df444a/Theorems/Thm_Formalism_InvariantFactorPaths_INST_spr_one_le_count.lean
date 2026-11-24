-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_INST_spr_one_le_count
-- name    : Formalism.InvariantFactorPaths.INST.spr_one_le_count
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:15.843288+00:00
-- url     : https://prove2.me/theorems/c5e42889-fd9c-4612-a08f-fa32613ed409
-- title:
--   INST: spr one le count
-- statement:
--   The INST construction uses the spr one le count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/Spread.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/Spread.lean#L40-L47

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

theorem Formalism.InvariantFactorPaths.INST.spr_one_le_count {n s : ℕ} (I : Fin s → Fin n) (hI : Function.Injective I) (hs : s = n) (a : Fin n) :
    1 ≤ ∑ q : Fin s, (Pi.single (I q) 1 : Fin n → ℕ) a := by sorry
