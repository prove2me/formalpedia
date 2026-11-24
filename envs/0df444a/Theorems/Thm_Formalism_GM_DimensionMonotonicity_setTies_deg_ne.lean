-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_setTies_deg_ne
-- name    : Formalism.GM.DimensionMonotonicity.setTies_deg_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:41.066797+00:00
-- url     : https://prove2.me/theorems/aaf1d935-6a10-4fea-a296-d22fbfce4156
-- title:
--   Dimension Monotonicity: set Ties deg ne
-- statement:
--   The Dimension Monotonicity construction uses the set Ties deg ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2545-L2555
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2545-L2555

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

theorem Formalism.GM.DimensionMonotonicity.setTies_deg_ne (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (n : Fin T.t → ℕ)
    (n' : ℕ) (b : Fin N) (hb : (b : ℕ) ≠ T.pos i + 1) :
    (LL.setTies T (Function.update n i n')).deg b = (LL.setTies T n).deg b := by sorry
