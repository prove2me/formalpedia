-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AnisotropicColumnSums_chat_gen
-- name    : Formalism.FourierDecayAlt.P.AnisotropicColumnSums.chat_gen
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:29:15.699801+00:00
-- url     : https://prove2.me/theorems/b64f8128-8a5d-431e-a738-f2898030efbb
-- title:
--   Anisotropic Column Sums: chat gen
-- statement:
--   The Anisotropic Column Sums construction uses the chat gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AnisotropicColumnSums.lean#L19-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AnisotropicColumnSums.lean#L19-L33

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
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
open Formalism.FourierDecayAlt.P.AnisotropicColumnSums

theorem Formalism.FourierDecayAlt.P.AnisotropicColumnSums.chat_gen (t n : ℕ) (h : t = n + 1) (A : Type) [Ring A] [Algebra ℂ A] (Eop : Fin t → Fin t → A)
    (P Q : Matrix (Fin t) (Fin t) ℂ) (la : Fin t) (hla : la.val = n) (ι : Fin n → Fin t)
    (hι : ∀ a, (ι a).val = a.val) (hE : GlRel Eop) (hQP : Q * P = 1) (hPQ : P * Q = 1) (u : ℂ) (β : Fin t → ℂ)
    (hβ : ∀ j, j ≠ la → (β ᵥ* P) j = 0) :
    chatA Eop u (fun p => P p la) β = (β ᵥ* P) la • qminor (Econj Eop P Q) ι ι u := by sorry
