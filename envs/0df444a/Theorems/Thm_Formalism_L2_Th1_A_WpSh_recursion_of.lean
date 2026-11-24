-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_WpSh_recursion_of
-- name    : Formalism.L2.Th1.A.WpSh.recursion_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:48.020676+00:00
-- url     : https://prove2.me/theorems/9e4d8dad-e4e0-4bc7-825e-0fdb3baf77f6
-- title:
--   Wp Sh: recursion of
-- statement:
--   The Wp Sh construction uses the recursion of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/WpShape.lean#L302-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/WpShape.lean#L302-L317

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

theorem Formalism.L2.Th1.A.WpSh.recursion_of [CharZero K] {c : K} {r : K⟦X⟧}
    (h : X ^ 2 * derivative K (derivative K r) = 12 * r + X ^ 2 * (6 * (r * r)) - X ^ 2 * C c)
    (h0 : coeff 0 r = 0) (hodd : ∀ n, Odd n → coeff n r = 0) (q : ℕ) (hq : 1 ≤ q) :
    ((q : K) - 1) * (2 * (q : K) + 5) * coeff (2 * q + 2) r =
      3 * ∑ i ∈ Finset.Icc 1 (q - 1), coeff (2 * i) r * coeff (2 * (q - i)) r := by sorry
