-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_indep_B
-- name    : Formalism.GM.DimensionMonotonicity.indep_B
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:07.986256+00:00
-- url     : https://prove2.me/theorems/4424a9b8-c1bd-4d45-9c98-c6dec6ff8498
-- title:
--   Dimension Monotonicity: indep B
-- statement:
--   The Dimension Monotonicity construction uses the indep B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1276-L1307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1276-L1307

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

theorem Formalism.GM.DimensionMonotonicity.indep_B (j0 : ℕ) (s : Finset (Fin N × Fin r →₀ ℕ)) (a : (Fin N × Fin r →₀ ℕ) → MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hs : ∀ b ∈ s, ∀ v : Fin N × Fin r, (v.1 : ℕ) < j0 → b v = 0)
    (ha : ∀ b ∈ s, ∀ m ∈ (a b).support, ∀ v : Fin N × Fin r, j0 ≤ (v.1 : ℕ) → m v = 0)
    (h0 : ∑ b ∈ s, a b * monomial b 1 = 0) : ∀ b ∈ s, a b = 0 := by sorry
