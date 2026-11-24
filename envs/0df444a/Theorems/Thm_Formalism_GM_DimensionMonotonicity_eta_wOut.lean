-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_eta_wOut
-- name    : Formalism.GM.DimensionMonotonicity.eta_wOut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:38.366831+00:00
-- url     : https://prove2.me/theorems/98f5b73a-7c26-4d1d-b9d2-de61b6d15ffa
-- title:
--   Dimension Monotonicity: eta w Out
-- statement:
--   The Dimension Monotonicity construction uses the eta w Out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2565-L2570
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2565-L2570

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.DimensionMonotonicity.eta_wOut (iK : Fin N) (ρ : Fin r) (u : ℕ) :
    IsWeightedHomogeneous (wOut N r iK) (X (iK, ρ) ^ u : MvPolynomial (Fin N × Fin r) ℚ_[p]) 0 := by sorry
