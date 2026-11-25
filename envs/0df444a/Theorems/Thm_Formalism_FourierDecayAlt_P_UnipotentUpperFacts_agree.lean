-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentUpperFacts_agree
-- name    : Formalism.FourierDecayAlt.P.UnipotentUpperFacts.agree
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:29:31.098112+00:00
-- url     : https://prove2.me/theorems/44b3fcdc-eb48-5b57-8a7e-45cd8aa7188a
-- title:
--   Unipotent Upper Facts: agree
-- statement:
--   The Unipotent Upper Facts construction uses the agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentUpperFacts.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentUpperFacts.lean#L18-L29

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
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

theorem Formalism.FourierDecayAlt.P.UnipotentUpperFacts.agree (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (hΓ : IsUnit (Vᴴ * H * V).det) (A B : Matrix n n ℂ)
    (hV : A * V = B * V) (hU : ∀ x, (Vᴴ * H) *ᵥ x = 0 → A *ᵥ x = B *ᵥ x) : A = B := by sorry
