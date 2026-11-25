-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FlagGramRestriction_KU_V
-- name    : Formalism.FourierDecayAlt.P.FlagGramRestriction.KU_V
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:28:51.656488+00:00
-- url     : https://prove2.me/theorems/f94b7505-c58c-4f68-979a-6fac07f47d9c
-- title:
--   Flag Gram Restriction: KU V
-- statement:
--   The Flag Gram Restriction construction uses the KU V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagGramRestriction.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagGramRestriction.lean#L86-L90

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FlagGramRestriction
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.FlagGramRestriction.KU_V {z z' : Fin (2 * r + k + 1) → ℂ} {γ κ : B.Mat k r} (hκ : κ ∈ C2.KU k r z z' γ) :
    κ * gnB k r z z' γ = gnB k r z z' γ := by sorry
