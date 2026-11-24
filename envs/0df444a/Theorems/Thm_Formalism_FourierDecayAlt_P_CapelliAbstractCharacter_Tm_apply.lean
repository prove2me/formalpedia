-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_Tm_apply
-- name    : Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.Tm_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:56:19.572043+00:00
-- url     : https://prove2.me/theorems/311fd448-3e11-4f8f-a826-8d39fa90501f
-- title:
--   Capelli Abstract Character: Tm apply
-- statement:
--   The Capelli Abstract Character construction uses the Tm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliAbstractCharacter.lean#L261-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliAbstractCharacter.lean#L261-L264

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
variable {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V)

theorem Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.Tm_apply (w : ℂ) (j l : Fin (N + 1)) (y : V) :
    Tm E w j l y = (if j = l then w • y else 0) + E j l y := by sorry
