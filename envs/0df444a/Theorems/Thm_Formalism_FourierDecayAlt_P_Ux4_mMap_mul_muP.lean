-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_mMap_mul_muP
-- name    : Formalism.FourierDecayAlt.P.Ux4.mMap_mul_muP
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:22:34.907736+00:00
-- url     : https://prove2.me/theorems/d0f9ac17-e786-46e0-ba9e-240ba0799a64
-- title:
--   Ux4: m Map mul mu P
-- statement:
--   The Ux4 construction uses the m Map mul mu P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L202-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L202-L206

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

theorem Formalism.FourierDecayAlt.P.Ux4.mMap_mul_muP (Z W : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k ρ) :
    mMap k j ρ Z γ * muP k j ρ W = mMap k j ρ (Z * W) γ := by sorry
