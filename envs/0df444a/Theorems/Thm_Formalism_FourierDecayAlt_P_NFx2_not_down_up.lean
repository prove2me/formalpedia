-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_not_down_up
-- name    : Formalism.FourierDecayAlt.P.NFx2.not_down_up
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:18:07.533136+00:00
-- url     : https://prove2.me/theorems/05c70643-63f0-411a-a054-f6ccbfd50ad5
-- title:
--   NFx2: not down up
-- statement:
--   The NFx2 construction uses the not down up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L226-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L226-L233

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

theorem Formalism.FourierDecayAlt.P.NFx2.not_down_up (P : M.Par) {i j l : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1))
    (hl : l ∈ Icc 1 (P.k - 1)) {τ μ σ : M.Ty P} (h1 : M.Up P i μ τ) (h2 : M.Up P j μ σ) (h3 : M.Up P l τ σ) : False := by sorry
