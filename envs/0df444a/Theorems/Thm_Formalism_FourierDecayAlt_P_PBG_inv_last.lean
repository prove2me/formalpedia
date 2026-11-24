-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_inv_last
-- name    : Formalism.FourierDecayAlt.P.PBG.inv_last
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:38:58.207026+00:00
-- url     : https://prove2.me/theorems/a77f7ac1-0deb-4a3b-9da5-001d3f418074
-- title:
--   PBG: inv last
-- statement:
--   The PBG construction uses the inv last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHead.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHead.lean#L72-L75

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainFirstIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal

theorem Formalism.FourierDecayAlt.P.PBG.inv_last {m : ℕ} (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hZ : Z.det ≠ 0) (b : Fin (m + 1)) :
    Z⁻¹ b (Fin.last m) = Z.det⁻¹ * ((-1) ^ (m + (b : ℕ)) * (Z.submatrix Fin.castSucc b.succAbove).det) := by sorry
