-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_count_box
-- name    : Formalism.FourierDecayAlt.P.Herglotz.count_box
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:24.130142+00:00
-- url     : https://prove2.me/theorems/eb567159-ead6-43bb-8d4d-d771174ee54c
-- title:
--   Herglotz: count box
-- statement:
--   The Herglotz construction uses the count box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Herglotz.lean#L49-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Herglotz.lean#L49-L93

import Definitions.Def_Formalism_HermitianCurvature_StatementH
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Herglotz
open Real Filter Topology Finset
variable {d : ℕ}

theorem Formalism.FourierDecayAlt.P.Herglotz.count_box (N : ℕ) (τ : Fin d → ℤ) :
    (((box d N ×ˢ box d N).filter (fun p => p.1 - p.2 = τ)).card) =
      ∏ j, ((N : ℤ) - |τ j|).toNat := by sorry
