-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_mem_Gd
-- name    : Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.mem_Gd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:55:07.509681+00:00
-- url     : https://prove2.me/theorems/c4082255-7b86-4214-ba76-dbb993339866
-- title:
--   Capelli Abstract Character: mem Gd
-- statement:
--   The Capelli Abstract Character construction uses the mem Gd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliAbstractCharacter.lean#L248-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliAbstractCharacter.lean#L248-L250

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

theorem Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.mem_Gd {v : V} {X : Fin (N + 1) → V} :
    X ∈ Gd E v ↔ ∃ η : Fin (N + 1) → Module.End ℂ V, IsCov E η ∧ ∀ j, X j = η j v := by sorry
