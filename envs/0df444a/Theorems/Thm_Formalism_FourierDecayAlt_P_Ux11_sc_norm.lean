-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_sc_norm
-- name    : Formalism.FourierDecayAlt.P.Ux11.sc_norm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:24:43.060228+00:00
-- url     : https://prove2.me/theorems/82e7e81a-b9cc-4310-9ba9-defb86f9933f
-- title:
--   Ux11: sc norm
-- statement:
--   The Ux11 construction uses the sc norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean#L338-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean#L338-L340

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakToStrongSmoothnessReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux11
variable {k ρ mm : ℕ} {E V : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V]
  [NormedSpace ℂ V] {a : ℝ} {S : Set (B.Mat k ρ)}

theorem Formalism.FourierDecayAlt.P.Ux11.sc_norm (c : ℝ) (hc : 0 ≤ c) : ‖sc E c‖ ≤ c := by sorry
