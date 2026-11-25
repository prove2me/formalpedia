-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_poly_AAop
-- name    : Formalism.FourierDecayAlt.P.PBG.poly_AAop
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:19:47.036535+00:00
-- url     : https://prove2.me/theorems/5ed706b1-3d36-499a-965d-98ffef638cfe
-- title:
--   PBG: poly AAop
-- statement:
--   The PBG construction uses the poly AAop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L272-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L272-L289

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
include hU₀

theorem Formalism.FourierDecayAlt.P.PBG.poly_AAop (m : ℕ) (hm : m ≤ r) (f : Wsm (E := E) U₀) (g₀ : Mat k r) (hg : g₀ ∈ U₀)
    (hgG : g₀ ∈ GV k r) :
    PolyRepN m (fun u => C3.AAop k r m hm u f.1 g₀)
      ((Matrix.of fun a b : Fin m => xi0 g₀ (Fin.castLE hm a) (C3.xR k r m hm b)).det • f.1 g₀) := by sorry
