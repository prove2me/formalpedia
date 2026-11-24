-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_polyVanish
-- name    : Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.polyVanish
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:56:03.002489+00:00
-- url     : https://prove2.me/theorems/02c2f35e-6c9d-4ac8-b0b3-f19e74bc30c8
-- title:
--   Capelli Abstract Character: poly Vanish
-- statement:
--   The Capelli Abstract Character construction uses the poly Vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliAbstractCharacter.lean#L94-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliAbstractCharacter.lean#L94-L115

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

theorem Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.polyVanish {X : Type} [AddCommGroup X] [Module ℂ X] (d : ℕ) (c : ℕ → X) (F : Finset ℂ)
    (h : ∀ u : ℂ, u ∉ F → ∑ s ∈ Finset.range d, (u ^ s) • c s = 0) : ∀ s ∈ Finset.range d, c s = 0 := by sorry
