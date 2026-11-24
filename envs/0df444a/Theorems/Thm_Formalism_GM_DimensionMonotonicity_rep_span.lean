-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_rep_span
-- name    : Formalism.GM.DimensionMonotonicity.rep_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:27:43.148817+00:00
-- url     : https://prove2.me/theorems/7737dcf3-1e6a-4eef-a34b-c054adc65d07
-- title:
--   Dimension Monotonicity: rep span
-- statement:
--   The Dimension Monotonicity construction uses the rep span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2355-L2393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2355-L2393

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

theorem Formalism.GM.DimensionMonotonicity.rep_span (VF : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) (j0 : ℕ)
    {z : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hz : z ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ VF, ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)},
      x = g * q}) :
    ∃ s : Finset (Fin N × Fin r →₀ ℕ), ∃ a : (Fin N × Fin r →₀ ℕ) → MvPolynomial (Fin N × Fin r) ℚ_[p],
      (∀ b ∈ s, ∀ v : Fin N × Fin r, (v.1 : ℕ) < j0 → b v = 0) ∧ (∀ b, a b ∈ VF) ∧
        z = ∑ b ∈ s, a b * monomial b 1 := by sorry
