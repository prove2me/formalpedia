-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_dsum
-- name    : Formalism.FourierDecayAlt.P.Herglotz.dsum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:46:48.793091+00:00
-- url     : https://prove2.me/theorems/b0cef6a6-b0a2-4fa1-9c23-8ed0d398bdd2
-- title:
--   Herglotz: dsum
-- statement:
--   The Herglotz construction uses the dsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Herglotz.lean#L34-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Herglotz.lean#L34-L47

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

theorem Formalism.FourierDecayAlt.P.Herglotz.dsum (F : (Fin d → ℤ) → ℂ) (S : Finset (Fin d → ℤ)) :
    ∑ σ ∈ S, ∑ σ' ∈ S, F (σ - σ') =
      ∑' τ, (((S ×ˢ S).filter (fun p => p.1 - p.2 = τ)).card : ℂ) * F τ := by sorry
