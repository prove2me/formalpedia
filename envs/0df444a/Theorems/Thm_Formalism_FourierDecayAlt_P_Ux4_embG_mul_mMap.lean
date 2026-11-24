-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_embG_mul_mMap
-- name    : Formalism.FourierDecayAlt.P.Ux4.embG_mul_mMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:28:58.424674+00:00
-- url     : https://prove2.me/theorems/c4fe7b5c-f891-445b-95e3-3a5dc643e9c5
-- title:
--   Ux4: emb G mul m Map
-- statement:
--   The Ux4 construction uses the emb G mul m Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L196-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L196-L200

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

theorem Formalism.FourierDecayAlt.P.Ux4.embG_mul_mMap (Z : Matrix (Fin j) (Fin j) ℂ) (γ y : B.Mat k ρ) :
    embG k j ρ y * mMap k j ρ Z γ = mMap k j ρ Z (y * γ) := by sorry
