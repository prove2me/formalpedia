-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentUpperFacts_N_upper
-- name    : Formalism.FourierDecayAlt.P.UnipotentUpperFacts.N_upper
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:27:57.812815+00:00
-- url     : https://prove2.me/theorems/e2a92f0b-b1b5-446b-b7e8-f684025bd043
-- title:
--   Unipotent Upper Facts: N upper
-- statement:
--   The Unipotent Upper Facts construction uses the N upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentUpperFacts.lean#L58-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentUpperFacts.lean#L58-L91

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

theorem Formalism.FourierDecayAlt.P.UnipotentUpperFacts.N_upper {g : B.Mat k r} (hg : g ∈ Nset k r) (i j : Fin (2 * r + k + 1)) (hji : j ≤ i) :
    g i j = if i = j then 1 else 0 := by sorry
