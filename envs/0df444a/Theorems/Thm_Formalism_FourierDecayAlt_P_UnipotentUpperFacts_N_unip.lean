-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentUpperFacts_N_unip
-- name    : Formalism.FourierDecayAlt.P.UnipotentUpperFacts.N_unip
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:48:14.129318+00:00
-- url     : https://prove2.me/theorems/232269be-213c-4508-ab23-91895a2a1a39
-- title:
--   Unipotent Upper Facts: N unip
-- statement:
--   The Unipotent Upper Facts construction uses the N unip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentUpperFacts.lean#L93-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentUpperFacts.lean#L93-L96

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedPointsGramVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
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
open Formalism.FourierDecayAlt.P.UnipotentUpperFacts
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.UnipotentUpperFacts.N_unip {g : B.Mat k r} (hg : g ∈ Nset k r) : (g - 1) ^ (2 * r + k + 1) = 0 := by sorry
