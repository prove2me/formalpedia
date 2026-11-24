-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_ss_pj_up
-- name    : Formalism.FourierDecayAlt.P.NFx2.ss_pj_up
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:23:18.855938+00:00
-- url     : https://prove2.me/theorems/cb38da6d-13b6-4e01-a461-ccbe87f0e87c
-- title:
--   NFx2: ss pj up
-- statement:
--   The NFx2 construction uses the ss pj up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L362-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L362-L368

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

theorem Formalism.FourierDecayAlt.P.NFx2.ss_pj_up {SS : ℕ → A} (hR : Raises κ SS) {l : ℕ} {ρ ρ' : M.Ty P} (h : M.Up P l ρ ρ') :
    proj κ ρ' * SS l = SS l * proj κ ρ := by sorry
