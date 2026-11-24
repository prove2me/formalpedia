-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_mMap_mul_embG
-- name    : Formalism.FourierDecayAlt.P.Ux4.mMap_mul_embG
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:28:02.335404+00:00
-- url     : https://prove2.me/theorems/3cd0f5c7-e620-4f3f-ad0e-a1408ade3fd9
-- title:
--   Ux4: m Map mul emb G
-- statement:
--   The Ux4 construction uses the m Map mul emb G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L190-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L190-L194

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
variable {k j ρ : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux4.mMap_mul_embG (Z : Matrix (Fin j) (Fin j) ℂ) (γ y : B.Mat k ρ) :
    mMap k j ρ Z γ * embG k j ρ y = mMap k j ρ Z (γ * y) := by sorry
