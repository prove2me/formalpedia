-- Prove2me | Theorems.Thm_Formalism_REAL_abs_compactHalfSum_le
-- name    : Formalism.REAL.abs_compactHalfSum_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:20:06.149861+00:00
-- url     : https://prove2.me/theorems/4e77ccbe-6efa-4839-8215-814b2580ba6b
-- title:
--   REAL: abs compact Half Sum le
-- statement:
--   The REAL construction uses the abs compact Half Sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IsCompactInvariantOrthogonalInf.lean#L181-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IsCompactInvariantOrthogonalInf.lean#L181-L191

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantOrthogonalInf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.abs_compactHalfSum_le {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : |rhoC ε a| ≤ n := by sorry
