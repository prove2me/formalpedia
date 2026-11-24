-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_kappa_le_height_bound
-- name    : Formalism.InvariantFactorPaths.PW.kappa_le_height_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:10.199692+00:00
-- url     : https://prove2.me/theorems/def99ac9-f514-40b9-9b1f-a9c14f9d3e54
-- title:
--   PW: kappa le height bound
-- statement:
--   The PW construction uses the kappa le height bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/Discharge.lean#L99-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/Discharge.lean#L99-L110

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementF
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_Discharge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M Formalism.GM

theorem Formalism.InvariantFactorPaths.PW.kappa_le_height_bound : ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (a : ℕ) (κ : ℝ),
    (∀ x, LL.deg x ≤ 2 * a) → 2 * a * N + r ≤ p ^ 2 * (8 * a + r) ^ 2 →
    ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ → kapC p r LL.total ≤ ⌈κ / (N + 2)⌉₊ := by sorry
