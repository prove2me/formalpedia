-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_wt_eq
-- name    : Formalism.FourierDecayAlt.P.Herglotz.wt_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:47:06.306118+00:00
-- url     : https://prove2.me/theorems/7c8bf489-07c7-4f37-a33c-1f8a7d307225
-- title:
--   Herglotz: wt eq
-- statement:
--   The Herglotz construction uses the wt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Herglotz.lean#L141-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Herglotz.lean#L141-L148

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

theorem Formalism.FourierDecayAlt.P.Herglotz.wt_eq (N : ℕ) (hN : N ≠ 0) (τ : Fin d → ℤ) :
    (((N : ℝ) ^ d)⁻¹ * (((box d N ×ˢ box d N).filter (fun p => p.1 - p.2 = τ)).card : ℝ))
      = wt N τ := by sorry
