-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_EntryMinorBounds_minor_le
-- name    : Formalism.FourierDecayAlt.P.EntryMinorBounds.minor_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:12:56.982693+00:00
-- url     : https://prove2.me/theorems/7972bbea-c85e-4d21-bc3d-06fed3b1e2e5
-- title:
--   Entry Minor Bounds: minor le
-- statement:
--   The Entry Minor Bounds construction uses the minor le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryMinorBounds.lean#L58-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryMinorBounds.lean#L58-L72

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryMinorBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.EntryMinorBounds

theorem Formalism.FourierDecayAlt.P.EntryMinorBounds.minor_le {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (I J : Finset (Fin m)) :
    ‖C2.minorS M I J‖ ≤ (Nat.factorial m : ℝ) * (1 + C2.mx M) ^ m := by sorry
