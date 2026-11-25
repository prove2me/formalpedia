-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_Th_eigen
-- name    : Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.Th_eigen
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:55:12.602265+00:00
-- url     : https://prove2.me/theorems/5dc03464-b563-4708-abba-9e68c54a7599
-- title:
--   Capelli Abstract Character: Th eigen
-- statement:
--   The Capelli Abstract Character construction uses the Th eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliAbstractCharacter.lean#L376-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliAbstractCharacter.lean#L376-L410

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

theorem Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.Th_eigen (hE : GlRel E) {m : Fin (N + 1) → ℂ} {v : V} (hv : v ∈ CapSp E m) (i : Fin (N + 1))
    {Y : Fin (N + 1) → V} (hY : Y ∈ Gd E v) (hK : KK E Y = (-m i) • Y) (u : ℂ) :
    Th E u Y = (∏ j ∈ Finset.univ.erase i, (u + m j)) • Y := by sorry
