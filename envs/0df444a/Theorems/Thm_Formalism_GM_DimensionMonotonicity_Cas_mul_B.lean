-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_Cas_mul_B
-- name    : Formalism.GM.DimensionMonotonicity.Cas_mul_B
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:45:46.959342+00:00
-- url     : https://prove2.me/theorems/94296d23-7e59-43b8-bfab-967e7c6fcbbb
-- title:
--   Dimension Monotonicity: Cas mul B
-- statement:
--   The Dimension Monotonicity construction uses the Cas mul B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2327-L2335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2327-L2335

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

theorem Formalism.GM.DimensionMonotonicity.Cas_mul_B (LL : Letters N) (j0 : ℕ) (y q : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hq : ∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < j0 → m v = 0) :
    (GA p LL j0).Cas (y * q) = (GA p LL j0).Cas y * q := by sorry
