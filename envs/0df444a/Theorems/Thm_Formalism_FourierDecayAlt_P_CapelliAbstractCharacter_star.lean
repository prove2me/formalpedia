-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_star
-- name    : Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.star
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:55:03.990813+00:00
-- url     : https://prove2.me/theorems/bef80106-28b4-42e5-9a83-ba319a395d46
-- title:
--   Capelli Abstract Character: star
-- statement:
--   The Capelli Abstract Character construction uses the star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliAbstractCharacter.lean#L339-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliAbstractCharacter.lean#L339-L350

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

theorem Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.star (hE : GlRel E) {m : Fin (N + 1) → ℂ} {v : V} (hv : v ∈ CapSp E m) {X : Fin (N + 1) → V}
    (hX : X ∈ Gd E v) (u : ℂ) : u • Th E u X - Th E u (KK E X) = cpol m u • X := by sorry
