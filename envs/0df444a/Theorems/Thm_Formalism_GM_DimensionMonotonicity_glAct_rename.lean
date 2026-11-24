-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_rename
-- name    : Formalism.GM.DimensionMonotonicity.glAct_rename
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:37.15848+00:00
-- url     : https://prove2.me/theorems/6438c050-03b3-4b8a-9038-e158be69ebf6
-- title:
--   Dimension Monotonicity: gl Act rename
-- statement:
--   The Dimension Monotonicity construction uses the gl Act rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1206-L1214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1206-L1214

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

theorem Formalism.GM.DimensionMonotonicity.glAct_rename {M : ℕ} (LA : Letters M) (LB : Letters N) (ι : Fin M → Fin N) (hι : ∀ a, ((ι a) : ℕ) = a)
    (hv : ∀ a, LB.vec (ι a) = LA.vec a) (j : ℕ) (c d : Fin r) (F : MvPolynomial (Fin M × Fin r) ℚ_[p]) :
    rename (fun x => (ι x.1, x.2)) (glAct p LA j c d F) = glAct p LB j c d (rename (fun x => (ι x.1, x.2)) F) := by sorry
