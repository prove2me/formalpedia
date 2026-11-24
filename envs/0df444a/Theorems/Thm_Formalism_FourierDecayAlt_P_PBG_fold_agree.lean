-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_fold_agree
-- name    : Formalism.FourierDecayAlt.P.PBG.fold_agree
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:21:42.581018+00:00
-- url     : https://prove2.me/theorems/8b25e5b6-15db-43d5-8ca9-0039e64e6588
-- title:
--   PBG: fold agree
-- statement:
--   The PBG construction uses the fold agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L189-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L189-L201

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (U₀ : Set (Mat k r)) (hU₀ : IsOpen U₀)

theorem Formalism.FourierDecayAlt.P.PBG.fold_agree : ∀ (L : List (Module.End ℂ (Wsm (E := E) U₀) × ((Mat k r → E) → (Mat k r → E)))),
    (∀ p ∈ L, ∀ (h : Wsm (E := E) U₀), ∀ g ∈ U₀, g ∈ GV k r → (p.1 h).1 g = p.2 h.1 g) →
    (∀ p ∈ L, ∀ (h₁ h₂ : Mat k r → E), (∀ x ∈ U₀, x ∈ GV k r → h₁ x = h₂ x) →
      ∀ g ∈ U₀, g ∈ GV k r → p.2 h₁ g = p.2 h₂ g) →
    ∀ (f : Wsm (E := E) U₀), ∀ g ∈ U₀, g ∈ GV k r →
      ((L.map Prod.fst).prod f).1 g = (L.map Prod.snd).foldr (fun T h => T h) f.1 g
  := by sorry
