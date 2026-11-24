-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_blk_expand
-- name    : Formalism.FourierDecayAlt.P.NFx2.blk_expand
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:16:41.375329+00:00
-- url     : https://prove2.me/theorems/167a44b4-7c8d-460c-bacb-b01b13c04208
-- title:
--   NFx2: blk expand
-- statement:
--   The NFx2 construction uses the blk expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L308-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L308-L315

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (κ : (M.Ty P → ℂ) →ₐ[ℂ] A)

theorem Formalism.FourierDecayAlt.P.NFx2.blk_expand (X Y : A) (σ τ : M.Ty P) :
    proj κ σ * (X * Y) * proj κ τ = ∑ μ, (proj κ σ * X * proj κ μ) * (proj κ μ * Y * proj κ τ) := by sorry
