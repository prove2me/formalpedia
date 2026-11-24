-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_cprod_eig
-- name    : Formalism.GM.DimensionMonotonicity.cprod_eig
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:27:44.753362+00:00
-- url     : https://prove2.me/theorems/c674a4de-775c-4329-b8b7-6ba5596ad130
-- title:
--   Dimension Monotonicity: cprod eig
-- statement:
--   The Dimension Monotonicity construction uses the cprod eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2306-L2315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2306-L2315

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

theorem Formalism.GM.DimensionMonotonicity.cprod_eig {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
    {x : V} {e : ℤ} (hx : G.Cas x = ((e : ℤ) : K) • x) (cs : List ℤ) :
    G.cprod cs x = (cs.map (fun c => (((e - c : ℤ)) : K))).prod • x := by sorry
