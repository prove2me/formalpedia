-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_rho_succ
-- name    : Formalism.FourierDecayAlt.P.NFx2.rho_succ
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:20:00.149652+00:00
-- url     : https://prove2.me/theorems/75f1eea4-a9dd-4c78-b4af-de64847f97ca
-- title:
--   NFx2: rho succ
-- statement:
--   The NFx2 construction uses the rho succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L152-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L152-L154

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
open Formalism.FourierDecayAlt.M

theorem Formalism.FourierDecayAlt.P.NFx2.rho_succ (P : M.Par) (π : M.Ty P) (i : Fin (P.k - 1)) :
    M.rho P π ((i : ℕ) + 1) = P.lo ((i : ℕ) + 1) + (((π i : Fin _) : ℕ) : ℝ) := by sorry
