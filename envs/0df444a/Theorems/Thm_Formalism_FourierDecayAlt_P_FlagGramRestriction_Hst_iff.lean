-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FlagGramRestriction_Hst_iff
-- name    : Formalism.FourierDecayAlt.P.FlagGramRestriction.Hst_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:44:36.357237+00:00
-- url     : https://prove2.me/theorems/485b94bd-5f04-461e-b55e-44e725a6739c
-- title:
--   Flag Gram Restriction: Hst iff
-- statement:
--   The Flag Gram Restriction construction uses the Hst iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagGramRestriction.lean#L33-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagGramRestriction.lean#L33-L45

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

theorem Formalism.FourierDecayAlt.P.FlagGramRestriction.Hst_iff {z z' : Fin (2 * r + k + 1) → ℂ} {γ : B.Mat k r} (hγ : IsUnit γ.det) (h : B.Mat k r) :
    h ∈ C2.Hst k r z z' γ ↔ h ∈ Sset k r z ∧ γ⁻¹ * h * γ ∈ Sset k r z' := by sorry
