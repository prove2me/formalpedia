-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_det_upper_minor_eq_minor
-- name    : Formalism.FourierDecayAlt.P.PBG.det_upper_minor_eq_minor
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:19:13.758545+00:00
-- url     : https://prove2.me/theorems/5ba464d9-f184-417c-9567-525105ed52b8
-- title:
--   PBG: det upper minor eq minor
-- statement:
--   The PBG construction uses the det upper minor eq minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L319-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L319-L327

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

theorem Formalism.FourierDecayAlt.P.PBG.det_upper_minor_eq_minor (z z' : Fin (2 * r + k + 1) → ℂ) (g₀ : Mat k r) (m : ℕ) (hm : m ≤ r) :
    (Matrix.of fun a b : Fin m => xi0 g₀ (Fin.castLE hm a) (C3.xR k r m hm b)).det =
      Dmin k r z z' g₀ ⟨m, by omega⟩ := by sorry
