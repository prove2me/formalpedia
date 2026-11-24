-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_eta_wL
-- name    : Formalism.GM.DimensionMonotonicity.eta_wL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:23.098339+00:00
-- url     : https://prove2.me/theorems/58a4cfc0-9a51-41f4-ba2c-1b3eab191178
-- title:
--   Dimension Monotonicity: eta w L
-- statement:
--   The Dimension Monotonicity construction uses the eta w L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2557-L2563
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2557-L2563

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

theorem Formalism.GM.DimensionMonotonicity.eta_wL (iK : Fin N) (ρ : Fin r) (u : ℕ) :
    IsWeightedHomogeneous (wL N r) (X (iK, ρ) ^ u : MvPolynomial (Fin N × Fin r) ℚ_[p]) (Pi.single iK (u : ℤ)) := by sorry
