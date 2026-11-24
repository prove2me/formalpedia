-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_Norming_eq
-- name    : Formalism.FourierDecayAlt.P.Ux11.Norming.eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:24:42.940849+00:00
-- url     : https://prove2.me/theorems/f3f9ab1c-8813-4b0d-b202-eea882acbd3a
-- title:
--   Norming: eq
-- statement:
--   The Norming construction uses the eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean#L25-L28

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

theorem Formalism.FourierDecayAlt.P.Ux11.Norming.eq {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {lam : I → V →L[ℝ] E}
    (hN : Norming lam) {v w : V} (h : ∀ i, lam i v = lam i w) : v = w := by sorry
