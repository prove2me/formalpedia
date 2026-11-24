-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_up_idx
-- name    : Formalism.FourierDecayAlt.P.NFx2.up_idx
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:28:07.740722+00:00
-- url     : https://prove2.me/theorems/f25ed83d-544f-467d-a552-a6e55420ca8c
-- title:
--   NFx2: up idx
-- statement:
--   The NFx2 construction uses the up idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L199-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L199-L206

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

theorem Formalism.FourierDecayAlt.P.NFx2.up_idx (P : M.Par) {l l' : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) (hl' : l' ∈ Icc 1 (P.k - 1)) {π σ : M.Ty P}
    (h : M.Up P l π σ) (h' : M.Up P l' π σ) : l = l' := by sorry
