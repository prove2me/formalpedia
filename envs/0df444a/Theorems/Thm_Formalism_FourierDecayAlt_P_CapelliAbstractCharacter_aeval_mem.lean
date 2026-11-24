-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_aeval_mem
-- name    : Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.aeval_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:56:29.122803+00:00
-- url     : https://prove2.me/theorems/31ac9773-a2ef-4fe3-a799-25433717fc3e
-- title:
--   Capelli Abstract Character: aeval mem
-- statement:
--   The Capelli Abstract Character construction uses the aeval mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliAbstractCharacter.lean#L123-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliAbstractCharacter.lean#L123-L129

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.aeval_mem {W : Type} [AddCommGroup W] [Module ℂ W] (G : Submodule ℂ W) (K : Module.End ℂ W)
    (hK : ∀ X ∈ G, K X ∈ G) (p : ℂ[X]) : ∀ X ∈ G, Polynomial.aeval K p X ∈ G := by sorry
