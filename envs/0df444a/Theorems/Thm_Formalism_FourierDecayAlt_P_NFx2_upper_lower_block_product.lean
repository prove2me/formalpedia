-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_upper_lower_block_product
-- name    : Formalism.FourierDecayAlt.P.NFx2.upper_lower_block_product
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:18:11.811803+00:00
-- url     : https://prove2.me/theorems/f10ca51e-45a5-4c85-9a09-739074c53685
-- title:
--   NFx2: upper lower block product
-- statement:
--   The NFx2 construction uses the upper lower block product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L2378-L2408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L2378-L2408

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}

theorem Formalism.FourierDecayAlt.P.NFx2.upper_lower_block_product (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hR : Raises κ SS) {l : ℕ}
    (hl : l ∈ Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P} (hu : M.Up P l ρ ρ') (u w : ℂ) :
    proj κ ρ' * (QQ u 0 1 * QQ w 1 0) * proj κ ρ =
      M.xEx P {l} ρ w • ((L0.GG * xA κ u * (sc_LL h hF).m0 u) * (SS l * proj κ ρ)) := by sorry
