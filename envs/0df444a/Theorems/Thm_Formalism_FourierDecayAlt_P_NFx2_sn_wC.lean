-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_wC
-- name    : Formalism.FourierDecayAlt.P.NFx2.sn_wC
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:18:32.597888+00:00
-- url     : https://prove2.me/theorems/0dc18d88-acab-40d8-bff6-6622fc36af51
-- title:
--   NFx2: sn w C
-- statement:
--   The NFx2 construction uses the sn w C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L1359-L1385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L1359-L1385

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section

theorem Formalism.FourierDecayAlt.P.NFx2.sn_wC {P : M.Par} (hWE : M.WExact) (hP : P.OK) (τ : M.Ty P) {Y : ℂ} (hY1 : M.xC P τ (Y + 1) ≠ 0) :
    M.wC P τ Y = M.qC P Y / M.xC P τ (Y + 1) +
      ∑ j ∈ Icc 1 (P.k - 1), M.xEx P {j} τ Y / (Y + M.rho P τ j + 1) * ((M.Nrm P j τ : ℝ) : ℂ) := by sorry
