-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_transp_exch
-- name    : Formalism.FourierDecayAlt.P.Wd6.transp_exch
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:16:55.30369+00:00
-- url     : https://prove2.me/theorems/3d3f292a-7040-4ab4-ab4c-0b86d55ab0a8
-- title:
--   Wd6: transp exch
-- statement:
--   The Wd6 construction uses the transp exch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L268-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L268-L275

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {B : Type} [Ring B]

theorem Formalism.FourierDecayAlt.P.Wd6.transp_exch {X T : M2 B} {b : B} (hc : ∀ i j, EC (X i j) T)
    (h : X * T * (Matrix.diagonal fun _ => b) = (Matrix.diagonal fun _ => b) * T * X) :
    Tᵀ * Xᵀ * (Matrix.diagonal fun _ => b) = (Matrix.diagonal fun _ => b) * Xᵀ * Tᵀ := by sorry
