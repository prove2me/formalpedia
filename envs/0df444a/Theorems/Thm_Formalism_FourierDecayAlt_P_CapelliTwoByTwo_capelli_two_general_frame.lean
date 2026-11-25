-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliTwoByTwo_capelli_two_general_frame
-- name    : Formalism.FourierDecayAlt.P.CapelliTwoByTwo.capelli_two_general_frame
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:48:18.854836+00:00
-- url     : https://prove2.me/theorems/72d70d71-107a-48f7-aa8a-6c8b0797b801
-- title:
--   Capelli Two By Two: capelli two general frame
-- statement:
--   The Capelli Two By Two construction uses the capelli two general frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliTwoByTwo.lean#L22-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliTwoByTwo.lean#L22-L38

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliTwoByTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.CapelliTwoByTwo

theorem Formalism.FourierDecayAlt.P.CapelliTwoByTwo.capelli_two_general_frame (t n : ℕ) (h : t = n + 2) (A : Type) [Ring A] [Algebra ℂ A] (Eop : Fin t → Fin t → A)
    (P Q : Matrix (Fin t) (Fin t) ℂ) (i0 i1 : Fin t) (h0 : i0.val = 0) (h1 : i1.val = 1) (ι : Fin n → Fin t)
    (hι : ∀ a, (ι a).val = a.val + 2) (hE : GlRel Eop) (hQP : Q * P = 1) (hPQ : P * Q = 1) (u : ℂ) (β β' : Fin t → ℂ)
    (hβ : ∀ j : Fin t, 2 ≤ j.val → (β ᵥ* P) j = 0 ∧ (β' ᵥ* P) j = 0) :
    chat2A Eop u (fun p => P p i0) (fun p => P p i1) β β' =
      ((β ᵥ* P) i0 * (β' ᵥ* P) i1 - (β ᵥ* P) i1 * (β' ᵥ* P) i0) • qminor (Econj Eop P Q) ι ι u := by sorry
