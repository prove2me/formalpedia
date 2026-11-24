-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_eta
-- name    : Formalism.GM.DimensionMonotonicity.pol_eta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:01.177829+00:00
-- url     : https://prove2.me/theorems/94091b82-5aa3-4fdb-9482-92849f90c4d3
-- title:
--   Dimension Monotonicity: pol eta
-- statement:
--   The Dimension Monotonicity construction uses the pol eta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2582-L2598
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2582-L2598

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

theorem Formalism.GM.DimensionMonotonicity.pol_eta (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (n : Fin T.t → ℕ)
    (n' : ℕ) (hn : n i ≤ n') (ρ : Fin r)
    {z : MvPolynomial (Fin N × Fin r) ℚ_[p]} (L0 L1 : Letters N)
    (h0 : ∀ b : Fin N, (b : ℕ) ≠ T.pos i + 1 → L1.deg b = L0.deg b)
    (h1 : ∀ b : Fin N, (b : ℕ) = T.pos i + 1 → L0.deg b = n i ∧ L1.deg b = n')
    (hz : z ∈ Pol p r L0) :
    X (⟨T.pos i + 1, by have := hK_of_adm LL T hadm i; omega⟩, ρ) ^ (n' - n i) * z ∈ Pol p r L1 := by sorry
