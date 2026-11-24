-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_WpSh_sum_even
-- name    : Formalism.L2.Th1.A.WpSh.sum_even
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:00.031792+00:00
-- url     : https://prove2.me/theorems/58dc4ead-b605-4a7d-91ed-edaf59e80d35
-- title:
--   Wp Sh: sum even
-- statement:
--   The Wp Sh construction uses the sum even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/WpShape.lean#L270-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/WpShape.lean#L270-L300

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.WpSh
variable {K : Type u} [Field K]

theorem Formalism.L2.Th1.A.WpSh.sum_even (a : ℕ → K) (h0 : a 0 = 0) (hodd : ∀ n, Odd n → a n = 0) (q : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (2 * q), a p.1 * a p.2 =
      ∑ i ∈ Finset.Icc 1 (q - 1), a (2 * i) * a (2 * (q - i)) := by sorry
