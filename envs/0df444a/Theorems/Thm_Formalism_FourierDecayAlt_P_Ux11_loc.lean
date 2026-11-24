-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_loc
-- name    : Formalism.FourierDecayAlt.P.Ux11.loc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:24:47.144972+00:00
-- url     : https://prove2.me/theorems/9f8939c8-0863-42ca-99c0-71e9ee657831
-- title:
--   Ux11: loc
-- statement:
--   The Ux11 construction uses the loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean#L143-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean#L143-L148

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
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Formalism.FourierDecayAlt.P.Ux11.loc {Ω : Set X} {bd : X → ℝ} (hΩ : IsOpen Ω) (hbd : ContinuousOn bd Ω) {x₀ : X} (hx : x₀ ∈ Ω) :
    ∃ r > 0, ∀ y ∈ Metric.ball x₀ r, y ∈ Ω ∧ bd y ≤ bd x₀ + 1 := by sorry
