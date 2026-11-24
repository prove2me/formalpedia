-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_eabH_congr
-- name    : Formalism.FourierDecayAlt.P.PBG.eabH_congr
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:19:44.857068+00:00
-- url     : https://prove2.me/theorems/5f804a5c-35c6-4f04-9aef-3958f6236b0c
-- title:
--   PBG: eab H congr
-- statement:
--   The PBG construction uses the eab H congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L121-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L121-L125

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

theorem Formalism.FourierDecayAlt.P.PBG.eabH_congr (a b : Fin (2 * r + k + 1)) {f₁ f₂ : Mat k r → E} {V : Set (Mat k r)} (hV : IsOpen V)
    {g : Mat k r} (hg : g ∈ V) (hgG : g ∈ GV k r) (he : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) :
    EabH (Hpk k r) a b f₁ g = EabH (Hpk k r) a b f₂ g := by sorry
