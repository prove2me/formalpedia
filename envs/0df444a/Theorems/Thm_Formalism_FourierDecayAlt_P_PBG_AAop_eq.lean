-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_AAop_eq
-- name    : Formalism.FourierDecayAlt.P.PBG.AAop_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:20:56.098053+00:00
-- url     : https://prove2.me/theorems/d102e64a-5e54-45b2-bf89-eca53720dfc2
-- title:
--   PBG: AAop eq
-- statement:
--   The PBG construction uses the AAop eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L247-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L247-L257

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
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (U₀ : Set (Mat k r)) (hU₀ : IsOpen U₀)

theorem Formalism.FourierDecayAlt.P.PBG.AAop_eq (m : ℕ) (hm : m ≤ r) (u : ℂ) (f : Wsm (E := E) U₀) (g₀ : Mat k r) (hg : g₀ ∈ U₀)
    (hgG : g₀ ∈ GV k r) :
    C3.AAop k r m hm u f.1 g₀ = ((C3.AAx k r (fun a b => EHt (E := E) U₀ hU₀ a b) (xi0 g₀) m hm u) f).1 g₀ := by sorry
